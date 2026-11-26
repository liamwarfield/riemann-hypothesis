module

public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.PtsIntegrable
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ResolutionExistsOfResolutionStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseVectorProperties
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ContDiffAtSmoothOnProj
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionFamilyDefectFormula
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockLUFactorization
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockMapFrameRestrictionRegular

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegrableOfResolutionStatement
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegrableOfResolutionStatement
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem ptsIntegrable_of_resK :
    ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → PtsIntegrableStatement :=
  fun h => GroundTheory.Heights₂.Heights.ForSecondHalf.PtsIntegrable.of_resExists (GlobalTheory.T.resolution_exists_of_resolution_statement h)

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegrableOfResolutionStatementStatement
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.points_integrable_of_resolution_statement : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → PtsIntegrableStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.ptsIntegrable_of_resK | exact GlobalTheory.CompanionTheory.Ar.Giv.ptsIntegrable_of_resK | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.ptsIntegrable_of_resK <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseChartHolomorphicComposition
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseChartHolomorphicComposition
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

theorem lift_analyticAt {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)} {n e : ℕ}
    (R : AnLogRes P J n) {V : Set (Fin e → ℂ)} {bp : (Fin e → ℂ) → R.X} (hV : IsOpen V) (hc : ContinuousOn bp V)
    (ha : ∀ k, AnalyticOnNhd ℂ (R.A.chart k ∘ bp) (V ∩ bp ⁻¹' (R.A.chart k).source)) {u₀ : Fin e → ℂ} (hu : u₀ ∈ V)
    (p : Σ k, ι k) : AnalyticAt ℂ (fun u => R.lift (bp u₀) (bp u) p) u₀ := by
  obtain ⟨k, hk⟩ := R.A.cover (bp u₀)
  have h1 : AnalyticAt ℂ (R.A.chart k ∘ bp) u₀ := ha k u₀ ⟨hu, hk⟩
  have h2 : AnalyticAt ℂ ((fun y => R.lift (bp u₀) y p) ∘ (R.A.chart k).symm) ((R.A.chart k ∘ bp) u₀) :=
    R.holo (bp u₀) p k _ ⟨(R.A.chart k).map_source hk, by
      show (R.A.chart k).symm (R.A.chart k (bp u₀)) ∈ R.U (bp u₀)
      rw [(R.A.chart k).left_inv hk]
      exact R.mem_U _⟩
  refine (h2.comp h1).congr ?_
  have hW : V ∩ bp ⁻¹' (R.A.chart k).source ∈ 𝓝 u₀ :=
    (hc.isOpen_inter_preimage hV (R.A.chart k).open_source).mem_nhds ⟨hu, hk⟩
  filter_upwards [hW] with u hu'
  simp only [Function.comp, (R.A.chart k).left_inv hu'.2]

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem bvec_analyticAt {M : FlagModel y Ψ N j} {n : ℕ} (BM : BaseMetric M n) (l : Fin BM.q) {e : ℕ}
    {V : Set (Fin e → ℂ)} {bp : (Fin e → ℂ) → BM.Rb.X} (hV : IsOpen V) (hc : ContinuousOn bp V)
    (ha : ∀ k, AnalyticOnNhd ℂ (BM.Rb.A.chart k ∘ bp) (V ∩ bp ⁻¹' (BM.Rb.A.chart k).source))
    (hO : ∀ u ∈ V, bp u ∈ BM.O l) {u₀ : Fin e → ℂ} (hu : u₀ ∈ V) (q : Σ k, baseIdx ι M.blk k) :
    AnalyticAt ℂ (fun u => FC.bvec BM l (bp u) q) u₀ := by
  have hne : BM.Rb.lift (bp u₀) (bp u₀) ⟨q.1, (BM.F l).c q.1⟩ ≠ 0 :=
    FibreCount.chart_ne ((BM.good l _ (hO u₀ hu)).1 q.1)
  have hq := (lift_analyticAt BM.Rb hV hc ha hu q).div
    (lift_analyticAt BM.Rb hV hc ha hu ⟨q.1, (BM.F l).c q.1⟩) hne
  refine hq.congr ?_
  have hW : V ∩ bp ⁻¹' (BM.Rb.U (bp u₀)) ∈ 𝓝 u₀ :=
    (hc.isOpen_inter_preimage hV (BM.Rb.isOpen_U _)).mem_nhds ⟨hu, BM.Rb.mem_U _⟩
  filter_upwards [hW] with u hu'
  obtain ⟨c, hc0, ec⟩ := BM.Rb.compat (bp u₀) (bp u) (bp u) ⟨hu'.2, BM.Rb.mem_U _⟩
  show BM.Rb.lift (bp u₀) (bp u) q / BM.Rb.lift (bp u₀) (bp u) ⟨q.1, (BM.F l).c q.1⟩ =
    BM.Rb.lift (bp u) (bp u) q / BM.Rb.lift (bp u) (bp u) ⟨q.1, (BM.F l).c q.1⟩
  rw [ec]
  exact mul_div_mul_left _ _ (hc0 q.1)

theorem valAt_analyticAt {M : FlagModel y Ψ N j} {n : ℕ} (BM : BaseMetric M n) (l : Fin BM.q) {e : ℕ}
    {V : Set (Fin e → ℂ)} {bp : (Fin e → ℂ) → BM.Rb.X} (hV : IsOpen V) (hO : ∀ u ∈ V, bp u ∈ BM.O l)
    {u₀ : Fin e → ℂ} (hu : u₀ ∈ V) (hw : ∀ q, AnalyticAt ℂ (fun u => FC.bvec BM l (bp u) q) u₀) {s : M.Ω}
    (hs : RegAt M.x (mCoordIdeal (FC.bvec BM l (bp u₀))) s) :
    AnalyticAt ℂ (fun u => valAt M.x s (FC.bvec BM l (bp u))) u₀ := by
  obtain ⟨d, g, h, hg, hh, hQ, eq⟩ := hs
  have hE : ∀ (z : (Σ k, baseIdx ι M.blk k) → ℂ) (f : MRing (baseIdx ι M.blk)),
      eval z (map (Int.castRingHom ℂ) f) = aeval z f := fun z f => by
    rw [aeval_def, algebraMap_int_eq, ← eval_map]
  have aG : AnalyticAt ℂ (fun u => aeval (FC.bvec BM l (bp u)) g) u₀ := AnalyticAt.aeval_mvPolynomial hw g
  have aH : AnalyticAt ℂ (fun u => aeval (FC.bvec BM l (bp u)) h) u₀ := AnalyticAt.aeval_mvPolynomial hw h
  have h0 : aeval (FC.bvec BM l (bp u₀)) h ≠ 0 := fun e0 => hQ (mem_mCoordIdeal_of_aeval_eq_zero _ hh e0)
  refine (aG.div aH h0).congr ?_
  filter_upwards [hV.mem_nhds hu, aH.continuousAt.eventually_ne h0] with u hu' hne
  have hz := (bvec_good K ι Φ y Ψ N j M n BM l _ (hO u hu')).1
  have h1 : eval (FC.bvec BM l (bp u)) (map (Int.castRingHom ℂ) h) ≠ 0 := by rwa [hE]
  have h2 : aeval M.x h ≠ 0 := fun e0 => h1 (hz.2 h (mem_mCoordIdeal_of_aeval_eq_zero M.x hh e0))
  have hv : IsValueAt M.x s (FC.bvec BM l (bp u))
      (eval (FC.bvec BM l (bp u)) (map (Int.castRingHom ℂ) g) / eval (FC.bvec BM l (bp u)) (map (Int.castRingHom ℂ) h)) :=
    ⟨d, g, h, hg, hh, h2, eq, h1, rfl⟩
  rw [valAt_eq hz hv, hE, hE]
  rfl

theorem bvec_val_analytic : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (l : Fin BM.q) (e : ℕ) (V : Set (Fin e → ℂ)) (bp : (Fin e → ℂ) → BM.Rb.X), IsOpen V → ContinuousOn bp V → (∀ k, AnalyticOnNhd ℂ (BM.Rb.A.chart k ∘ bp) (V ∩ bp ⁻¹' (BM.Rb.A.chart k).source)) → (∀ u ∈ V, bp u ∈ BM.O l) → (∀ q, AnalyticOnNhd ℂ (fun u => FC.bvec BM l (bp u) q) V) ∧ ∀ s : M.Ω, (∀ b ∈ BM.O l, RegAt M.x (mCoordIdeal (FC.bvec BM l b)) s) → AnalyticOnNhd ℂ (fun u => valAt M.x s (FC.bvec BM l (bp u))) V := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM l e V bp hV hc ha hO
  have hb : ∀ q, AnalyticOnNhd ℂ (fun u => FC.bvec BM l (bp u) q) V := fun q u hu =>
    bvec_analyticAt BM l hV hc ha hO hu q
  exact ⟨hb, fun s hs u hu => valAt_analyticAt BM l hV hO hu (fun q => hb q u hu) (hs _ (hO u hu))⟩

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseChartHolomorphicCompositionStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_chart_holomorphic_composition : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (l : Fin BM.q) (e : ℕ) (V : Set (Fin e → ℂ)) (bp : (Fin e → ℂ) → BM.Rb.X), IsOpen V → ContinuousOn bp V → (∀ k, AnalyticOnNhd ℂ (BM.Rb.A.chart k ∘ bp) (V ∩ bp ⁻¹' (BM.Rb.A.chart k).source)) → (∀ u ∈ V, bp u ∈ BM.O l) → (∀ q, AnalyticOnNhd ℂ (fun u => FC.bvec BM l (bp u) q) V) ∧ ∀ s : M.Ω, (∀ b ∈ BM.O l, RegAt M.x (mCoordIdeal (FC.bvec BM l b)) s) → AnalyticOnNhd ℂ (fun u => valAt M.x s (FC.bvec BM l (bp u))) V := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec_val_analytic | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec_val_analytic | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec_val_analytic <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.VerticalFactorSmoothHermitianMetric
section -- merged from Development.WeilBound.CoreStatements.PlurisubharmonicCones.VerticalFactorSmoothLine
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

namespace LevelTowerAlt

section

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem eval_conjVec (z : (Σ k, J k) → ℂ) (f : MRing J) :
    MvPolynomial.eval (conjVec z) (MvPolynomial.map (Int.castRingHom ℂ) f) =
      starRingEnd ℂ (MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) f)) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp, conjVec]

theorem contDiff_conjVec : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, J k) → ℂ => conjVec z) :=
  contDiff_pi.2 fun i => Complex.conjCLE.contDiff.comp (contDiff_apply ℝ (fun _ => ℂ) i)

theorem conjVec_ne {z : (Σ k, J k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : ∀ k, ∃ i, conjVec z ⟨k, i⟩ ≠ 0 :=
  fun k => (hz k).imp fun _ hi => (map_ne_zero _).2 hi

noncomputable def symmLine (Z : HermLine J) : HermLine J where
  a := Z.a
  h z := Real.sqrt (Z.h z * Z.h (conjVec z))
  pos z hz := Real.sqrt_pos.2 (mul_pos (Z.pos z hz) (Z.pos _ (conjVec_ne hz)))
  smul c z hc := by
    have h1 : conjVec (fun p : Σ k, J k => c p.1 * z p) =
        fun p : Σ k, J k => (fun k => starRingEnd ℂ (c k)) p.1 * conjVec z p := by
      funext p
      simp [conjVec]
    have h2 := Z.smul (fun k => starRingEnd ℂ (c k)) (conjVec z) fun k => (map_ne_zero _).2 (hc k)
    have hP := prod_norm_zpow_pos hc Z.a
    rw [h1, h2, Z.smul c z hc]
    simp only [Complex.norm_conj]
    rw [_root_.mul_mul_mul_comm, Real.sqrt_mul (mul_self_nonneg _), Real.sqrt_mul_self hP.le]

theorem symmLine_smooth {Z : HermLine J} (hZ : IsSmoothHerm Z) : IsSmoothHerm (symmLine Z) :=
  ContDiffOn.sqrt (ContDiffOn.mul hZ (ContDiffOn.comp hZ contDiff_conjVec.contDiffOn fun _ hz => conjVec_ne hz))
    fun z hz => (mul_pos (Z.pos z hz) (Z.pos _ (conjVec_ne hz))).ne'

theorem symmLine_conj (Z : HermLine J) : IsConjInvariantH (symmLine Z) := by
  intro z
  show Real.sqrt (Z.h (conjVec z) * Z.h (conjVec (conjVec z))) = Real.sqrt (Z.h z * Z.h (conjVec z))
  rw [SncPiece.conj_conj, mul_comm]

end

theorem vertical_factor_smooth_line : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W), ∀ p ∈ D.S, (∃ A : HermLine J, A.a = D.vdeg p ∧ IsSmoothHerm A ∧ IsConjInvariantH A ∧ ∀ z ∈ mcPts (mCoordIdeal D.y), A.h z = D.vertFactor p z) ∧ ∀ a, ∀ t ∈ Metric.ball (0 : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) 1, ∃ G : (Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) → ℂ, AnalyticAt ℂ G t ∧ ∀ᶠ t' in 𝓝 t, Real.log (D.vertFactor p ((D.chart a).γ t')) = (G t').re := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D p hp
  have hpos := VertFactorPos.proof II Ψ K J Ω W D p hp
  have hsm := VertFactorSmooth.proof VertFactorPos.proof II Ψ K J Ω W D p hp
  constructor
  · obtain ⟨Z, hZa, hZs, hZ⟩ := HermExtend.proof K J (mCoordIdeal D.y) (D.vdeg p) (D.vertFactor p) D.arith.2.1.2.1
      hpos hsm.1 hsm.2
    refine ⟨symmLine Z, hZa, symmLine_smooth hZs, symmLine_conj Z, fun z hz => ?_⟩
    have hconj : D.vertFactor p (conjVec z) = D.vertFactor p z := by
      obtain ⟨dG, dH, G, H, hG, hH, hdeg, hrel, hHz⟩ := VertFactorSmooth.exists_forms D hp hz
      rw [VertFactorSmooth.vertFactor_eq D hp (SncPiece.conj_mem hz) hG hH hdeg hrel
          (by rw [eval_conjVec]; exact (map_ne_zero _).2 hHz),
        VertFactorSmooth.vertFactor_eq D hp hz hG hH hdeg hrel hHz, eval_conjVec, eval_conjVec, ← map_div₀,
        Complex.norm_conj]
    show Real.sqrt (Z.h z * Z.h (conjVec z)) = _
    rw [hZ z hz, hZ _ (SncPiece.conj_mem hz), hconj, Real.sqrt_mul_self (hpos z hz).le]
  · intro a t ht
    have hz := (D.chart a).mem t ht
    obtain ⟨dG, dH, G, H, hG, hH, hdeg, hrel, hHz⟩ := VertFactorSmooth.exists_forms D hp hz
    have hγ := (D.chart a).analytic t ht
    have hev : ∀ f : MRing J, AnalyticAt ℂ
        (fun t' => MvPolynomial.eval ((D.chart a).γ t') (MvPolynomial.map (Int.castRingHom ℂ) f)) t := fun f =>
      AnalyticAt.comp (g := fun z => MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) f))
        (AnalyticOnNhd.eval_mvPolynomial _ _ (Set.mem_univ _)) hγ
    have h0 := hpos _ hz
    rw [VertFactorSmooth.vertFactor_eq D hp hz hG hH hdeg hrel hHz] at h0
    obtain ⟨L, hL, hLe⟩ := exists_log_re ((hev G).div (hev H) hHz) (norm_pos_iff.1 h0)
    refine ⟨L, hL, ?_⟩
    filter_upwards [hLe, (hev H).continuousAt.eventually_ne hHz, Metric.isOpen_ball.mem_nhds ht] with t' h1 h2 h3
    rw [VertFactorSmooth.vertFactor_eq D hp ((D.chart a).mem t' h3) hG hH hdeg hrel h2]
    exact h1

end LevelTowerAlt
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.VerticalFactorSmoothHermitianMetric
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.vertical_factor_smooth_hermitian_metric : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W), ∀ p ∈ D.S, (∃ A : HermLine J, A.a = D.vdeg p ∧ IsSmoothHerm A ∧ IsConjInvariantH A ∧ ∀ z ∈ mcPts (mCoordIdeal D.y), A.h z = D.vertFactor p z) ∧ ∀ a, ∀ t ∈ Metric.ball (0 : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) 1, ∃ G : (Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) → ℂ, AnalyticAt ℂ G t ∧ ∀ᶠ t' in 𝓝 t, Real.log (D.vertFactor p ((D.chart a).γ t')) = (G t').re := by
  first | exact @LevelTowerAlt.vertical_factor_smooth_line | exact LevelTowerAlt.vertical_factor_smooth_line
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.VerticalFactorSmoothHermitianMetricStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vertical_factor_smooth_hermitian_metric : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W), ∀ p ∈ D.S, (∃ A : HermLine J, A.a = D.vdeg p ∧ IsSmoothHerm A ∧ IsConjInvariantH A ∧ ∀ z ∈ mcPts (mCoordIdeal D.y), A.h z = D.vertFactor p z) ∧ ∀ a, ∀ t ∈ Metric.ball (0 : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) 1, ∃ G : (Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) → ℂ, AnalyticAt ℂ G t ∧ ∀ᶠ t' in 𝓝 t, Real.log (D.vertFactor p ((D.chart a).γ t')) = (G t').re := by
  first | exact @GlobalTheory.CompanionTheory.Relay.vertical_factor_smooth_hermitian_metric | exact GlobalTheory.CompanionTheory.Relay.vertical_factor_smooth_hermitian_metric | (intros; apply GlobalTheory.CompanionTheory.Relay.vertical_factor_smooth_hermitian_metric <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagPointInMultiprojectivePoints
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagPointInMultiprojectivePoints
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

theorem flagPt_mem_mcPts : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (l : Fin BM.q), ∀ b ∈ BM.O l, ∀ h : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ', IsBlockDiag j (h τ') ∧ (h τ').det ≠ 0) → FC.flagPt M (BM.F l) (FC.bvec BM l b) h ∈ mcPts (mCoordIdeal y) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM l b hb h hh
  obtain ⟨hmem, hgood, hnorm, -⟩ := FC.bvec_good K ι Φ y Ψ N j M n BM l b hb
  have e := basePart_flagPt M (BM.F l) (FC.bvec BM l b) h
  refine CPts.flag_back M (BM.isFrame l) (by rw [e]; exact hmem) (by rw [e]; exact hgood) (h := h)
    ⟨fun k => by rw [e]; exact hnorm k, hh, fun p k hp => ⟨1, one_ne_zero, fun m => ?_⟩⟩
  rw [e, one_mul]
  exact flagPt_step M (BM.F l) (FC.bvec BM l b) h hp m

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagPointInMultiprojectivePointsStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_point_in_multiprojective_points : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (l : Fin BM.q), ∀ b ∈ BM.O l, ∀ h : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ', IsBlockDiag j (h τ') ∧ (h τ').det ≠ 0) → FC.flagPt M (BM.F l) (FC.bvec BM l b) h ∈ mcPts (mCoordIdeal y) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.flagPt_mem_mcPts | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.flagPt_mem_mcPts | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.flagPt_mem_mcPts <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentArithVarietyFirst
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentArithVarietyFirst
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.WMem

section Mat

variable {N j : ℕ}

theorem transv_isBlockDiag {a b ca cb : Fin N} (hb : (b : ℕ) = a + 1) (hab : (b : ℕ) < j ∨ j ≤ (a : ℕ))
    (hca : (ca : ℕ) = lastCol N j a) (hcb : (cb : ℕ) = ca + 1) (t : ℂ) :
    IsBlockDiag j (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) := by
  have same : ((ca : ℕ) < N - j ↔ (cb : ℕ) < N - j) := by
    have := a.2
    have := b.2
    have := cb.2
    unfold lastCol at hca
    split_ifs at hca <;> omega
  intro r s hrs
  have e1 : r ≠ s := fun e => hrs (by rw [e])
  rw [Matrix.add_apply, Matrix.one_apply_ne e1, zero_add, Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact hrs same.symm

theorem transv_det_one {ca cb : Fin N} (hc : (cb : ℕ) = ca + 1) (t : ℂ) :
    (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ).det = 1 := by
  have hne : ca ≠ cb := fun e => by rw [e] at hc; omega
  have hlt : ca < cb := by rw [Fin.lt_def]; omega
  rw [Matrix.det_of_lowerTriangular _ fun r c h => ?_]
  · refine Finset.prod_eq_one fun c _ => ?_
    rw [Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply_of_ne, add_zero]
    rintro ⟨rfl, e⟩
    exact hne e
  · have h' : r < c := h
    rw [Matrix.add_apply, Matrix.one_apply_ne h'.ne, Matrix.single_apply_of_ne, add_zero]
    rintro ⟨rfl, rfl⟩
    exact lt_asymm h' hlt

end Mat

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem isFlagOf_flagPt (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) {b : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hb : ∀ k, b ⟨k, F.c k⟩ = 1) {h : Ψ → Matrix (Fin N) (Fin N) ℂ}
    (hh : ∀ τ, IsBlockDiag j (h τ) ∧ (h τ).det ≠ 0) : M.IsFlagOf F (flagPt M F b h) h := by
  refine ⟨fun k => by rw [basePart_flagPt]; exact hb k, hh, fun p k hp => ⟨1, one_ne_zero, fun m => ?_⟩⟩
  rw [basePart_flagPt, flagPt_step M F b h hp m, one_mul]

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (d : ℕ) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (d + 2) → ∀ (l : Fin BM.q), ∀ b' ∈ BM.O l, ∀ (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (t : ℂ), (∀ τ', IsBlockDiag j (h τ') ∧ (h τ').det ≠ 0) → FC.wVec M (BM.F l) (FC.bvec BM l b') h τ a k₀ ca cb t ∈ mcPts (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM d τ a b k₀ ca cb hb hab hk hca hcb hvar l b' hb' h t hh
  obtain ⟨h1, h2⟩ := GlobalTheory.T.flag_adjacent_plucker_orbit K ι Φ y Ψ N j M τ a b k₀ ca cb hb hab hk hca hcb (BM.F l) (bvec BM l b') h t
  obtain ⟨g1, g2, g3, -⟩ := GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec_good K ι Φ y Ψ N j M n BM l b' hb'
  have hh' : ∀ τ', IsBlockDiag j (Function.update h τ (h τ * (1 + Matrix.single cb ca t)) τ') ∧
      (Function.update h τ (h τ * (1 + Matrix.single cb ca t)) τ').det ≠ 0 := by
    intro τ'
    by_cases e : τ' = τ
    · subst e
      rw [Function.update_self]
      refine ⟨(hh τ').1.mul (transv_isBlockDiag hb hab hca hcb t), ?_⟩
      rw [Matrix.det_mul, transv_det_one hcb, mul_one]
      exact (hh τ').2
    · rw [Function.update_of_ne e]
      exact hh τ'
  have hbase : basePart M.blk (fstPt k₀ (wVec M (BM.F l) (bvec BM l b') h τ a k₀ ca cb t)) = bvec BM l b' := by
    rw [h1, basePart_flagPt]
  refine (GlobalTheory.T.log_period_statement K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hab hk hca hcb hvar (BM.F l) _ (BM.isFrame l)
    (by rw [hbase]; exact g1) (by rw [hbase]; exact g2) (by rw [hbase]; exact g3)).2 ⟨h, t, ?_, ?_⟩
  · rw [h1]
    exact isFlagOf_flagPt M (BM.F l) g3 hh
  · rw [h2]
    exact isFlagOf_flagPt M (BM.F l) g3 hh'

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.WMem
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentArithVarietyFirstStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_arith_variety_first : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (d : ℕ) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (d + 2) → ∀ (l : Fin BM.q), ∀ b' ∈ BM.O l, ∀ (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (t : ℂ), (∀ τ', IsBlockDiag j (h τ') ∧ (h τ').det ≠ 0) → FC.wVec M (BM.F l) (FC.bvec BM l b') h τ a k₀ ca cb t ∈ mcPts (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.WMem.main | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.WMem.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.WMem.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsFlagPointInOrbit
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsFlagPointInOrbit
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

private theorem sameOrbit_symm_metric {K : Type} {ι : K → Type} {z z' : (Σ k, ι k) → ℂ}
    (h : SameOrbit z z') : SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
  funext p
  show z' p = (c p.1)⁻¹ * (c p.1 * z' p)
  rw [← mul_assoc, inv_mul_cancel₀ (hc p.1), one_mul]

private theorem sameOrbit_trans_metric {K : Type} {ι : K → Type} {z z' z'' : (Σ k, ι k) → ℂ}
    (h1 : SameOrbit z z') (h2 : SameOrbit z' z'') : SameOrbit z z'' := by
  obtain ⟨c, hc, rfl⟩ := h1
  obtain ⟨d, hd, rfl⟩ := h2
  refine ⟨fun k => c k * d k, fun k => mul_ne_zero (hc k) (hd k), ?_⟩
  funext p
  show c p.1 * (d p.1 * z'' p) = c p.1 * d p.1 * z'' p
  rw [mul_assoc]

theorem exists_flagPt_of_orbit : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (l : Fin BM.q), ∀ b ∈ BM.O l, ∀ z ∈ mcPts (mCoordIdeal y), SameOrbit (basePart M.blk z) (BM.Rb.lift b b) → ∃ h : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ', IsBlockDiag j (h τ') ∧ (h τ').det ≠ 0) ∧ SameOrbit z (FC.flagPt M (BM.F l) (FC.bvec BM l b) h) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM l b hb z hz hzb
  obtain ⟨hβmem, hβgood, hβc, hβorb⟩ := bvec_good K ι Φ y Ψ N j M n BM l b hb
  have h1 : SameOrbit (basePart M.blk z) (bvec BM l b) :=
    sameOrbit_trans_metric hzb (sameOrbit_symm_metric hβorb)
  obtain ⟨d, hd, hdz⟩ := id h1
  have hne : ∀ k, basePart M.blk z ⟨k, (BM.F l).c k⟩ ≠ 0 := by
    intro k
    rw [hdz]
    show d k * bvec BM l b ⟨k, (BM.F l).c k⟩ ≠ 0
    rw [hβc k, mul_one]
    exact hd k
  obtain ⟨z₁, hz₁z, hz₁c⟩ := GlobalTheory.CompanionTheory.Ar.PB.FibreCount.exists_normal_base M.blk (BM.F l).c z hne
  have hb1 : SameOrbit (basePart M.blk z₁) (bvec BM l b) :=
    sameOrbit_trans_metric (GlobalTheory.CompanionTheory.Ar.PB.FibreCount.basePart_orbit M.blk hz₁z) h1
  have hbeq : basePart M.blk z₁ = bvec BM l b := by
    obtain ⟨e, he, hez⟩ := hb1
    have he1 : ∀ k, e k = 1 := by
      intro k
      have hk := congrFun hez ⟨k, (BM.F l).c k⟩
      have hk' : basePart M.blk z₁ ⟨k, (BM.F l).c k⟩ = e k * bvec BM l b ⟨k, (BM.F l).c k⟩ := hk
      rw [hz₁c k, hβc k, mul_one] at hk'
      exact hk'.symm
    rw [hez]
    funext p
    show e p.1 * bvec BM l b p = bvec BM l b p
    rw [he1, one_mul]
  have hz₁ : z₁ ∈ mcPts (mCoordIdeal y) := by
    obtain ⟨c, hc, hcz⟩ := id hz₁z
    refine ⟨?_, ?_⟩
    · intro k
      obtain ⟨i, hi⟩ := hz.1 k
      refine ⟨i, ?_⟩
      rw [hcz]
      exact mul_ne_zero (hc k) hi
    · intro f hf
      have hf' : f ∈ mCoordIdeal z₁ := by
        rw [GlobalTheory.CompanionTheory.Ar.PB.FibreCount.mCoordIdeal_eq_of_orbit hz₁z]
        exact GlobalTheory.CompanionTheory.Ar.PB.CPts.mCoordIdeal_le hz hf
      exact eval_eq_zero_of_mem_mCoordIdeal hf'
  have hgood : M.GoodAt (BM.F l) (mCoordIdeal (basePart M.blk z₁)) := by
    rw [hbeq]
    exact hβgood
  obtain ⟨h, hflag⟩ := GlobalTheory.CompanionTheory.Ar.PB.CPts.flag_fwd M (BM.isFrame l) hz₁ hgood hz₁c
  obtain ⟨_, hhb, hblocks⟩ := hflag
  refine ⟨h, hhb, ?_⟩
  have h2 : SameOrbit z₁ (flagPt M (BM.F l) (bvec BM l b) h) := by
    apply GlobalTheory.CompanionTheory.Ar.PB.FibreCount.sameOrbit_of_blocks M.blk
    · rw [basePart_flagPt, hbeq]
    · intro p k hpk
      obtain ⟨a, ha, hza⟩ := hblocks p k hpk
      refine ⟨a, ha, fun m => ?_⟩
      rw [hza m, flagPt_step M (BM.F l) (bvec BM l b) h hpk m, hbeq]
  exact sameOrbit_trans_metric (sameOrbit_symm_metric hz₁z) h2

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsFlagPointInOrbitStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flag_point_in_orbit : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (l : Fin BM.q), ∀ b ∈ BM.O l, ∀ z ∈ mcPts (mCoordIdeal y), SameOrbit (basePart M.blk z) (BM.Rb.lift b b) → ∃ h : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ', IsBlockDiag j (h τ') ∧ (h τ').det ≠ 0) ∧ SameOrbit z (FC.flagPt M (BM.F l) (FC.bvec BM l b) h) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.exists_flagPt_of_orbit | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.exists_flagPt_of_orbit | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.exists_flagPt_of_orbit <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PtsIntegralLogNormRatEqBase
section -- merged from Development.WeilBound.CoreStatements.PluriharmonicCharts.XReBridge
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace PositivityTheory.Xgp.re_bridge

theorem isC2At_of_isPotential {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {Q : LocPot X}
    (h : IsPotential A Q) (x : X) : IsTwiceDifferentiableAt A Q x := by
  intro j hj
  refine potSmoothAt A Q h x j ⟨(A.chart j).map_source hj, ?_⟩
  show (A.chart j).symm (A.chart j x) ∈ Q.U x
  rw [(A.chart j).left_inv hj]
  exact Q.mem_U x

theorem isNull_union {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {N N' : Set X}
    (h : IsNull A N) (h' : IsNull A N') : IsNull A (N ∪ N') := by
  intro j
  rw [Set.preimage_union, Set.inter_union_distrib_left]
  exact measure_union_null (h j) (h' j)

theorem isNull_zeros {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)} {D : ℕ}
    (R : AnLogRes P J D) (hP : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (D + 1)) {s : MRing ι} {a : K → ℕ} (hs : IsMultiHomog s a)
    (hsP : s ∉ P) : IsNull R.A {x | eval (R.lift x x) (map (Int.castRingHom ℂ) s) = 0} := by
  obtain ⟨Ψ, hΨ⟩ := goodProjExists K ι P D hP
  exact fun j => GlobalTheory.CompanionTheory.Ar.Cmp.OneSlot.zeros_null R Ψ hP hΨ hs hsP j

end PositivityTheory.Xgp.re_bridge

theorem PositivityTheory.Xgp.t_re_bridge : ResExistsStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (D : ℕ) (R : AnLogRes P J D) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas D X) (π : R.X → X) (hπ : HoloMap R.A A π) (dg : ℕ) (br : Set X), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (D + 1) → IsDegreeOff A R.A π dg br → ∀ (L : Fin D → HermLine ι) (Φ : Fin D → LocPot X), (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPotential A (Φ j)) → (∀ j, SamePot R.A Set.univ (potOf R (L j)) ((Φ j).pullback π hπ.1)) → ∀ (Am : HermLine ι) (f g : MRing ι) (u : X → ℝ) (N : Set R.X), IsSmoothHerm Am → IsRatSectionOn P Am f g → IsNull R.A N → (∀ x ∉ N, logNormRat Am f g (R.lift x x) = u (π x)) → MIntegrable A Φ u → ptsIntegral P (pot L) (logNormRat Am f g) = dg * mInt A Φ u := by
  intro hE K _ ι _ P J D R X _ _ _ A π hπ dg br hP hdeg L Φ hL hΦ hS Am f g u N hAm hfg hN hu hI
  obtain ⟨α, β, hf, hg, hfP, hgP, hαβ⟩ := hfg
  have hB : IsSmoothHerm (HermLine.sqMetric (ι := ι) β) := isSmoothHerm_sqMetric β
  have hAB := ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_tensor hAm hB
  have hsf : IsSectionOn P (Am.tensor (HermLine.sqMetric β)) f := by
    refine ⟨α, fun k => ?_, hf, hfP⟩
    show Am.a k + (β k : ℤ) = α k
    rw [← hαβ k]
    ring
  have hsg : IsSectionOn P (HermLine.sqMetric (ι := ι) β) g := ⟨β, fun k => rfl, hg, hgP⟩
  have hQ : ∀ j, IsPotential R.A (potOf R (L j)) := fun j => isPotential_potOf R (hL j)
  rw [GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionIntegral.ptsIntegral_logNormRat
      (GroundTheory.Heights₂.Heights.ForSecondHalf.PtsIntegrable.of_resExists hE) hP hL hAm hB hsf hsg,
    ptsIntegral_eq_mInt' hE resBridge R hP hL hAB hsf, ptsIntegral_eq_mInt' hE resBridge R hP hL hB hsg,
    ← (degreeFormulaInt A R.A π hπ dg br hdeg Φ hΦ u hI).2]
  have hlin := mIntLinear R.A _ hQ (-1) _ _ (brIntegrable R L _ g hP hL hB hsg)
    (brIntegrable R L _ f hP hL hAB hsf)
  have hnull := PositivityTheory.Xgp.re_bridge.isNull_union hN (PositivityTheory.Xgp.re_bridge.isNull_union
    (PositivityTheory.Xgp.re_bridge.isNull_zeros R hP hf hfP) (PositivityTheory.Xgp.re_bridge.isNull_zeros R hP hg hgP))
  have key := (mInt_congr_samePot D R.X R.A
    (N ∪ ({x | eval (R.lift x x) (map (Int.castRingHom ℂ) f) = 0} ∪
      {x | eval (R.lift x x) (map (Int.castRingHom ℂ) g) = 0}))ᶜ
    (fun j => potOf R (L j)) (fun j => (Φ j).pullback π hπ.1)
    (fun x => -1 * logNorm (HermLine.sqMetric β) g (R.lift x x) +
      logNorm (Am.tensor (HermLine.sqMetric β)) f (R.lift x x)) (u ∘ π)
    (by rwa [compl_compl]) (fun j x _ => hS j x (Set.mem_univ x))
    (fun j x _ => PositivityTheory.Xgp.re_bridge.isC2At_of_isPotential R.A
      (isPotentialPullback A R.A π hπ _ (hΦ j)) x) ?_).1
  · rw [← key, hlin]
    ring
  · intro x hx
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, not_or] at hx
    obtain ⟨hxN, hxf, hxg⟩ := hx
    have hz := (R.mem x x (R.mem_U x)).1
    have hf0 := norm_pos_iff.mpr hxf
    have hg0 := norm_pos_iff.mpr hxg
    have hA0 := Am.pos _ hz
    have hB0 := (HermLine.sqMetric (ι := ι) β).pos _ hz
    show _ = u (π x)
    rw [← hu x hxN]
    show -1 * Real.log (‖eval (R.lift x x) (map (Int.castRingHom ℂ) g)‖ / (HermLine.sqMetric β).h (R.lift x x)) +
      Real.log (‖eval (R.lift x x) (map (Int.castRingHom ℂ) f)‖ /
        (Am.h (R.lift x x) * (HermLine.sqMetric β).h (R.lift x x))) =
      Real.log (‖eval (R.lift x x) (map (Int.castRingHom ℂ) f)‖ /
        ‖eval (R.lift x x) (map (Int.castRingHom ℂ) g)‖ / Am.h (R.lift x x))
    rw [Real.log_div hf0.ne' (mul_pos hA0 hB0).ne', Real.log_mul hA0.ne' hB0.ne',
      Real.log_div hg0.ne' hB0.ne', Real.log_div (div_pos hf0 hg0).ne' hA0.ne',
      Real.log_div hf0.ne' hg0.ne']
    ring
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PtsIntegralLogNormRatEqBase
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem ptsIntegral_logNormRat_eq_base : ResExistsStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (D : ℕ) (R : AnLogRes P J D) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas D X) (π : R.X → X) (hπ : HoloMap R.A A π) (dg : ℕ) (br : Set X), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (D + 1) → IsDegreeOff A R.A π dg br → ∀ (L : Fin D → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (Φ : Fin D → LocPot X), (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPotential A (Φ j)) → (∀ j, SamePot R.A Set.univ (potOf R (L j)) ((Φ j).pullback π hπ.1)) → ∀ (Am : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (f g : MRing ι) (u : X → ℝ) (N : Set R.X), IsSmoothHerm Am → IsRatSectionOn P Am f g → IsNull R.A N → (∀ x ∉ N, logNormRat Am f g (R.lift x x) = u (π x)) → MIntegrable A Φ u → ptsIntegral P (pot L) (logNormRat Am f g) = dg * mInt A Φ u :=
  @PositivityTheory.Xgp.t_re_bridge

end GlobalTheory.CompanionTheory.Ar.PB
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PtsIntegralLogNormRatEqBaseStatement
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_number_pullback_degree_alt : ResExistsStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (D : ℕ) (R : AnLogRes P J D) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas D X) (π : R.X → X) (hπ : HoloMap R.A A π) (dg : ℕ) (br : Set X), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (D + 1) → IsDegreeOff A R.A π dg br → ∀ (L : Fin D → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (Φ : Fin D → LocPot X), (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPotential A (Φ j)) → (∀ j, SamePot R.A Set.univ (potOf R (L j)) ((Φ j).pullback π hπ.1)) → ∀ (Am : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (f g : MRing ι) (u : X → ℝ) (N : Set R.X), IsSmoothHerm Am → IsRatSectionOn P Am f g → IsNull R.A N → (∀ x ∉ N, logNormRat Am f g (R.lift x x) = u (π x)) → MIntegrable A Φ u → ptsIntegral P (pot L) (logNormRat Am f g) = dg * mInt A Φ u := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.ptsIntegral_logNormRat_eq_base | exact GlobalTheory.CompanionTheory.Ar.PB.ptsIntegral_logNormRat_eq_base | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.ptsIntegral_logNormRat_eq_base <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsPositivePotentialDominating
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsPositivePotentialDominating
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Cusp

section PosDom
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem potential_contDiffAt (A : FinHolAtlas e X) (P : LocPot X) (hP : IsPotential A P) (x : X)
    (j : Fin A.n) {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x) :
    ContDiffAt ℝ 2 (P.φ x ∘ (A.chart j).symm) y :=
  ((hP.1 x j).of_le two_le_infty).contDiffAt
    (((A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target
      (P.isOpen_U x)).mem_nhds hy)

theorem isPosPot_rsmul (A : FinHolAtlas e X) (P : LocPot X) (hP : IsPotential A P)
    (hpos : IsPosPot A P) {c : ℝ} (hc : 0 < c) : IsPosPot A (P.rsmul c) := by
  intro x j y hy w hw
  have h : levi ((P.rsmul c).φ x ∘ (A.chart j).symm) y w =
      c * levi (P.φ x ∘ (A.chart j).symm) y w :=
    TailChernBound.levi_smul' c (potential_contDiffAt A P hP x j hy) w
  rw [h]
  exact mul_pos hc (hpos x j y hy w hw)

theorem isPsh_add_rsmul_succ (A : FinHolAtlas e X) (Θ Φ : LocPot X) (hΘ : IsPotential A Θ)
    (hΘp : IsPosPot A Θ) (hΦ : IsPotential A Φ) (C : ℝ) (hC : IsPsh A (Θ.rsmul C + Φ)) :
    IsPsh A (Φ + LocPot.ofFun (fun _ => 0) + Θ.rsmul (C + 1)) := by
  intro x j y hy w
  have hyΦ : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Φ.U x := ⟨hy.1, hy.2.1.1⟩
  have hyΘ : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Θ.U x := ⟨hy.1, hy.2.2⟩
  have hΘa := potential_contDiffAt A Θ hΘ x j hyΘ
  have hΦa := potential_contDiffAt A Φ hΦ x j hyΦ
  have e1 : (Φ + LocPot.ofFun (fun _ => 0) + Θ.rsmul (C + 1)).φ x ∘ (A.chart j).symm =
      fun z => (C + 1) * (Θ.φ x ∘ (A.chart j).symm) z + 1 * (Φ.φ x ∘ (A.chart j).symm) z := by
    funext z
    show Φ.φ x _ + 0 + (C + 1) * Θ.φ x _ = (C + 1) * Θ.φ x _ + 1 * Φ.φ x _
    ring
  have e2 : (Θ.rsmul C + Φ).φ x ∘ (A.chart j).symm =
      fun z => C * (Θ.φ x ∘ (A.chart j).symm) z + 1 * (Φ.φ x ∘ (A.chart j).symm) z := by
    funext z
    show C * Θ.φ x _ + Φ.φ x _ = C * Θ.φ x _ + 1 * Φ.φ x _
    ring
  have h0 := hC x j y ⟨hy.1, hy.2.2, hy.2.1.1⟩ w
  rw [e2, TailChernBound.levi_lin C 1 hΘa hΦa w] at h0
  rw [e1, TailChernBound.levi_lin (C + 1) 1 hΘa hΦa w]
  have h1 : 0 ≤ levi (Θ.φ x ∘ (A.chart j).symm) y w :=
    TailBoundAlt.isPsh_of_isPosPot A Θ hΘp x j y hyΘ w
  linarith

end PosDom

theorem exists_posPot_dominating : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (M : XModel D) (Φ : ReciprocityTheory.AnForm.M.LocPot M.Xc), ReciprocityTheory.AnForm.M.IsPotential M.atlas Φ → ∃ Θ : ReciprocityTheory.AnForm.M.LocPot M.Xc, ReciprocityTheory.AnForm.M.IsPotential M.atlas Θ ∧ ReciprocityTheory.AnForm.M.IsPosPot M.atlas Θ ∧ ReciprocityTheory.AnForm.M.IsPsh M.atlas (Φ + ReciprocityTheory.AnForm.M.LocPot.ofFun (fun _ => 0) + Θ) := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D M Φ hΦ
  classical
  obtain ⟨Θ₀, hΘ₀, hloc⟩ := GlobalTheory.T.local_holomorphic_section_of_potential K J (mCoordIdeal D.y) D.n M D.A' D.A'_pos.1
  have hpos := GlobalTheory.T.local_section_of_potential_on_model II Ψ K J Ω W D M Θ₀ hΘ₀ hloc
  obtain ⟨C, hC0, hC, -⟩ := ReciprocityTheory.AnForm.P.TailBoundAlt.exists_psh_chern_bound M.atlas Θ₀ Φ hΘ₀ hpos hΦ
  exact ⟨Θ₀.rsmul (C + 1), ReciprocityTheory.AnForm.M.isPotentialRsmul M.atlas (C + 1) Θ₀ hΘ₀,
    isPosPot_rsmul M.atlas Θ₀ hΘ₀ hpos (by linarith),
    isPsh_add_rsmul_succ M.atlas Θ₀ Φ hΘ₀ hpos hΦ C hC⟩

end GlobalTheory.CompanionTheory.Ar.Cusp
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsPositivePotentialDominatingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_positive_potential_dominating : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (M : XModel D) (Φ : ReciprocityTheory.AnForm.M.LocPot M.Xc), ReciprocityTheory.AnForm.M.IsPotential M.atlas Φ → ∃ Θ : ReciprocityTheory.AnForm.M.LocPot M.Xc, ReciprocityTheory.AnForm.M.IsPotential M.atlas Θ ∧ ReciprocityTheory.AnForm.M.IsPosPot M.atlas Θ ∧ ReciprocityTheory.AnForm.M.IsPsh M.atlas (Φ + ReciprocityTheory.AnForm.M.LocPot.ofFun (fun _ => 0) + Θ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.exists_posPot_dominating | exact GlobalTheory.CompanionTheory.Ar.Cusp.exists_posPot_dominating | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.exists_posPot_dominating <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PRhoContinuous
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PRhoContinuous
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.PCont

theorem continuous_upV {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Kk : Type} [Fintype Kk]
    {ιk : Kk → Type} [∀ k, Fintype (ιk k)] (v : (Σ k, ιk k) → (Σ k, ι k)) :
    Continuous (upV v) := by
  refine continuous_pi fun q => ?_
  by_cases hq : ∃ q', v q' = q
  · simp only [upV, dif_pos hq]
    exact continuous_apply _
  · simp only [upV, dif_neg hq]
    exact continuous_const

theorem pSgn_ne_zero {Ψ : Type} {N j : ℕ} (hj : j ≤ N) (keep : Ψ × Fin N → Prop) (q : PIdx j keep) :
    pSgn (stepCols N j (pStep j keep q.1.1.1 q.1.1.2.2)) q.1.1.2.1 q.1.1.2.2 ≠ 0 := by
  obtain ⟨-, -, hb, ha, hc⟩ := GlobalTheory.T.pMat_stepCols_entry Ψ N j keep q hj
  have hX : IsLowerUni (pMat (j := j) keep (fun _ => (0 : ℂ)) q.1.1.1) := by
    refine ⟨fun a => ?_, fun a b hab => ?_⟩
    · unfold pMat lowMat
      rw [dif_neg (fun h => lt_irrefl _ h.1), if_pos rfl]
    · unfold pMat lowMat
      rw [dif_neg (fun h => lt_asymm hab h.1), if_neg hab.ne]
  exact (GlobalTheory.T.minorIJ_lowerUni_swap N _ _ _ _ hX ha hb q.1.2.1 (hc fun _ => 0).2).2

section Flag

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ PIdx j keep ≃ Fin e), IsPCtx M Rb keep κ v F kb V bl r h → ContinuousOn (pRho M Rb keep v F kb r h ε) (pO M Rb keep v F kb V r h) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb keep Kk _ ιk _ κ v F kb V bl r h ε H
  obtain ⟨hv, hcov, hF, hB, horb, hr, hh⟩ := H
  obtain ⟨hVo, hVt, -, -, hbl⟩ := hB
  have hbase : Set.MapsTo (pBase M v) (pO M Rb keep v F kb V r h) (mcPts (mCoordIdeal M.x)) := fun z hz =>
    (GlobalTheory.T.blockMap_frame_restriction K ι Φ y Ψ N j M keep Kk ιk κ v hv hcov).1 z hz.1
  have cU : Continuous (upV v) := continuous_upV v
  have cB : Continuous (pBase M v) := continuous_pi fun q =>
    (continuous_apply (⟨q.1.1, q.2⟩ : Σ k, ι k)).comp cU
  have hgood : ∀ z ∈ pO M Rb keep v F kb V r h, M.GoodAt F (mCoordIdeal (pBase M v z)) := by
    intro z hz
    have h3 := (hbl _ hz.2.2.1).2.2
    rw [(Rb.A.chart kb).left_inv hz.2.1] at h3
    have e := orbit_trans (orbit_symm (horb _ (hbase hz))) h3.2
    rw [GlobalTheory.CompanionTheory.Ar.PB.CovMap.mCoordIdeal_eq_of_sameOrbit e]
    exact h3.1
  intro z hz
  have hz₄ : ∀ p k, keep p → M.blk p = some k →
      twMinor M F (pBase M v z) p.2 k (h p.1)⁻¹ (upV v z) (stepCols N j p.2) ≠ 0 := hz.2.2.2
  refine continuousWithinAt_pi.2 fun i => ?_
  rcases e : ε.symm i with l | q
  · simp only [pRho, e]
    have c2 : ContinuousWithinAt (r ∘ pBase M v) (pO M Rb keep v F kb V r h) z :=
      ContinuousWithinAt.comp (hr _ (hbase hz)) cB.continuousWithinAt hbase
    have c3 : ContinuousAt (fun x => Rb.A.chart kb x l) ((r ∘ pBase M v) z) :=
      (continuous_apply l).continuousAt.comp ((Rb.A.chart kb).continuousAt hz.2.1)
    exact ContinuousAt.comp_continuousWithinAt (g := fun x => Rb.A.chart kb x l) c3 c2
  · simp only [pRho, e]
    obtain ⟨hk, -, -, -, -⟩ := GlobalTheory.T.pMat_stepCols_entry Ψ N j keep q M.j_le
    have cT := fun (k : K) (J : Finset (Fin N)) => twMinor_continuousWithinAt M F cB.continuousWithinAt hbase
      (hbase hz) (hgood z hz) cU.continuousWithinAt (pStep j keep q.1.1.1 q.1.1.2.2) k (h q.1.1.1)⁻¹ J
    cases e' : M.blk (q.1.1.1, pStep j keep q.1.1.1 q.1.1.2.2) with
    | none =>
      simp only [pRead, e', Option.elim_none]
      exact continuousWithinAt_const
    | some k =>
      simp only [pRead, e', Option.elim_some]
      have hd := mul_ne_zero (pSgn_ne_zero M.j_le keep q) (hz₄ _ k hk e')
      exact ContinuousWithinAt.div (cT k _) (ContinuousWithinAt.mul continuousWithinAt_const (cT k _)) hd

end Flag

end GlobalTheory.CompanionTheory.Ar.PB.PFl.PCont
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PRhoContinuousStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameData_local_norm_bound : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ PIdx j keep ≃ Fin e), IsPCtx M Rb keep κ v F kb V bl r h → ContinuousOn (pRho M Rb keep v F kb r h ε) (pO M Rb keep v F kb V r h) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.PFl.PCont.main | exact GlobalTheory.CompanionTheory.Ar.PB.PFl.PCont.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.PFl.PCont.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.UpVSmul
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.Cover

open GlobalTheory.CompanionTheory.Ar.PB.WMan.Cover GlobalTheory.CompanionTheory.Ar.PB.ValRing

section Scale

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Kk : Type} [Fintype Kk] {ιk : Kk → Type} [∀ k, Fintype (ιk k)]

theorem upV_smul {κ : Kk → K} {v : (Σ k, ιk k) → (Σ k, ι k)} (hb : IsBlockMap κ v) (c : K → ℂ)
    (z : (Σ k, ιk k) → ℂ) (q : Σ k, ι k) :
    upV v (fun p => c (κ p.1) * z p) q = c q.1 * upV v z q := by
  unfold upV
  by_cases h : ∃ q', v q' = q
  · rw [dif_pos h, dif_pos h]
    have e : κ h.choose.1 = q.1 := by
      rw [← hb.2.2.1, h.choose_spec]
    show c (κ h.choose.1) * z h.choose = _
    rw [e]
  · rw [dif_neg h, dif_neg h, mul_zero]

end Scale

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)), IsBlockMap κ v → (∀ k, k ∈ Set.range κ ↔ ((∀ p, M.blk p ≠ some k) ∨ ∃ p, keep p ∧ M.blk p = some k)) → ∀ z ∈ mcPts (mCoordIdeal (y ∘ v)), ∃ (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ), IsPCtx M Rb keep κ v F kb V bl r h ∧ z ∈ pO M Rb keep v F kb V r h := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n Rb keep Kk _ ιk _ κ v hbm hrange z hz
  obtain ⟨bs, -⟩ := GlobalTheory.T.blockMap_frame_restriction K ι Φ y Ψ N j M keep Kk ιk κ v hbm hrange
  obtain ⟨-, fr, -⟩ := CPts.main K ι Φ y Ψ N j M
  have hzb : pBase M v z ∈ mcPts (mCoordIdeal M.x) := bs z hz
  obtain ⟨F, hF, hG⟩ := fr _ hzb
  have hnon : Nonempty Rb.X := by
    obtain ⟨x, -⟩ := Rb.surj _ hzb fun h => by
      have := h.2 1 Submodule.mem_top
      simp at this
    exact ⟨x⟩
  obtain ⟨r, hr1, hr2⟩ := GlobalTheory.T.exists_continuous_orbit_section _ _ _ n Rb hnon
  have hx0 := hr1 _ hzb
  obtain ⟨kb, V, bl, hsrc, hV, hBC⟩ := GlobalTheory.T.exists_base_chart_at_good_point K ι Φ y Ψ N j M n Rb F (r (pBase M v z))
    (by rw [CovMap.mCoordIdeal_eq_of_sameOrbit hx0]; exact hG)
  obtain ⟨hblm, hblnorm, hblgood, hblorb⟩ := hBC.2.2.2.2 _ hV
  rw [(Rb.A.chart kb).left_inv hsrc] at hblorb
  generalize hzc : bl (Rb.A.chart kb (r (pBase M v z))) = zc at hblm hblnorm hblgood hblorb
  have horb : SameOrbit zc (pBase M v z) := orbit_trans (orbit_symm hblorb) hx0
  have hval : ∀ s, (∃ u, IsValueAt M.x s zc u) → valAt M.x s (pBase M v z) = valAt M.x s zc :=
    fun s hs => valAt_eq_of_orbit hblm hzb (orbit_symm horb) hs
  obtain ⟨c₀, hc₀, he⟩ := horb
  let c : K → ℂ := fun k => if h : ∀ p, M.blk p ≠ some k then c₀ ⟨k, h⟩ else 1
  have hc : ∀ k, c k ≠ 0 := fun k => by
    by_cases h : ∀ p, M.blk p ≠ some k
    · simp only [c, dif_pos h]
      exact hc₀ _
    · simp only [c, dif_neg h]
      exact one_ne_zero
  let z' : (Σ k, ιk k) → ℂ := fun p => c (κ p.1) * z p
  have hz' : z' ∈ mcPts (mCoordIdeal (y ∘ v)) :=
    mcPts_smul (CoordinateConeArithVar.isMultiHomogIdeal _) (fun k => c (κ k)) (fun k => hc _) hz
  have hbp : pBase M v z' = zc := by
    rw [he]
    funext q
    obtain ⟨⟨k, hk⟩, m⟩ := q
    show upV v z' ⟨k, m⟩ = c₀ ⟨k, hk⟩ * upV v z ⟨k, m⟩
    rw [upV_smul hbm c z ⟨k, m⟩]
    simp only [c, dif_pos hk]
  obtain ⟨h, hh, H⟩ := GlobalTheory.T.blockMap_frame_restriction_regular K ι Φ y Ψ N j M keep Kk ιk κ v hbm hrange F z' hF hz'
    (hbp ▸ hblgood) (hbp ▸ hblnorm)
  refine ⟨F, kb, V, bl, r, h, ⟨hbm, hrange, hF, hBC, hr1, hr2, hh⟩, hz, hsrc, ?_, ?_⟩
  · rw [hzc] at *
    exact hV
  · intro p k hkeep hp
    obtain ⟨A, hA0, hA'⟩ := H p k hkeep hp
    have hk : c k = 1 := dif_neg fun e => e p hp
    have hw : ∀ m : ι k, upV v z ⟨k, m⟩ =
        A * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (pBase M v z) * minorIJ (h p.1) I (stepCols N j p.2) := fun m => by
      have e : upV v z' ⟨k, m⟩ = upV v z ⟨k, m⟩ := by
        rw [upV_smul hbm c z ⟨k, m⟩]
        show c k * _ = _
        rw [hk, one_mul]
      rw [← e, hA' m, hbp]
      refine congrArg (fun s => A * s) (Finset.sum_congr rfl fun I _ => ?_)
      rw [hval _ (exists_isValueAt hblm (hblgood.2.1 _ I).1)]
    rw [twMinor_of_flag M hF hzb hG hp (hh p.1).1 hw, Matrix.nonsing_inv_mul _ (hh p.1).2.isUnit, CPts.minorIJ_one,
      mul_one]
    exact hA0

end GlobalTheory.CompanionTheory.Ar.PB.PFl.Cover
end
end
