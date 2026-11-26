module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegrableOfResolutionStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartFourth
public import ReciprocityTheory.AnalyticForms.PotentialTheory.HomogeneousLiftHolomorphicOnSnd

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RationalityOfResolutionStatement
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RationalityOfResolutionStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem ratR_of_resK :
    ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ReciprocityTheory.ChartRestriction.G.AI.I2.RatRStatement :=
  fun h => GroundTheory.Heights₂.Heights.Inter.RatR.proof (ptsIntegrable_of_resK h)

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RationalityOfResolutionStatementStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationality_of_resolution_statement : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ReciprocityTheory.ChartRestriction.G.AI.I2.RatRStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.ratR_of_resK | exact GlobalTheory.CompanionTheory.Ar.Giv.ratR_of_resK | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.ratR_of_resK <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameDataLocalIntegrability
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameDataLocalIntegrability
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.ChartRead

theorem chart_reads : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ PIdx j keep ≃ Fin e), IsPCtx M Rb keep κ v F kb V bl r h → ∀ w ∈ pD ε V, pPhi M F keep v bl h ε w ∈ pO M Rb keep v F kb V r h ∧ pRho M Rb keep v F kb r h ε (pPhi M F keep v bl h ε w) = w := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb keep Kk _ ιk _ κ v F kb V bl r h ε hc w hw
  obtain ⟨hflag, hbase, hread⟩ := GlobalTheory.T.frameData_local_resolution_open K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc w hw
  obtain ⟨z, hz, hzv, -⟩ := GlobalTheory.T.frameData_local_degree_estimate K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc w hw
  obtain ⟨hκ, -, hF, hBC, hr, -, hh⟩ := hc
  have hwV : pB ε w ∈ V := hw
  obtain ⟨hzb, -, hG, horb⟩ := hBC.2.2.2.2 _ hwV
  have hV : pB ε w ∈ (Rb.A.chart kb).target := hBC.2.1 hwV
  have hr1 : r (bl (pB ε w)) = (Rb.A.chart kb).symm (pB ε w) :=
    Rb.inj _ _ (fun hc => by simpa using hc.2 1 Submodule.mem_top) (orbit_trans (hr _ hzb) (orbit_symm horb))
  set φ := pPhi M F keep v bl h ε w with hφ
  have hMm : φ ∈ mcPts (mCoordIdeal (y ∘ v)) := by
    rw [← hzv]
    exact CPts.comp_mem_mcPts hκ (RingHom.id Φ) (x := y ∘ v) rfl hz
  have hL : ∀ τ, IsLowerUni (pMat keep (pL ε w) τ) := fun τ => WMan.Read.lowMat_lowerUni _ τ
  have hminor : ∀ (p : Ψ × Fin N) (k : K), keep p → M.blk p = some k → ∀ J : Finset (Fin N),
      twMinor M F (bl (pB ε w)) p.2 k (h p.1)⁻¹ (upV v φ) J =
        minorIJ (pMat keep (pL ε w) p.1) J (stepCols N j p.2) := fun p k hp hk J => by
    have := WMan.Read.twMinor_eq M hF hzb hG hk (hflag p.1).1 (hread p k hp hk) (h p.1)⁻¹ J
    rwa [show pH keep h ε p.1 w = h p.1 * pMat keep (pL ε w) p.1 from rfl,
      Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_iff_ne_zero.2 (hh p.1).2)] at this
  refine ⟨⟨hMm, ?_, ?_, ?_⟩, ?_⟩
  · rw [hbase, hr1]
    exact (Rb.A.chart kb).map_target hV
  · rw [hbase, hr1, (Rb.A.chart kb).right_inv hV]
    exact hwV
  · intro p k hp hk
    rw [hbase, hminor p k hp hk, WMan.Read.minor_self_of_lowerUni (hL p.1)]
    exact one_ne_zero
  · funext i
    obtain ⟨s, rfl⟩ := ε.surjective i
    unfold pRho
    rw [Equiv.symm_apply_apply]
    rcases s with l | q
    · show Rb.A.chart kb (r (pBase M v φ)) l = w (ε (Sum.inl l))
      rw [hbase, hr1, (Rb.A.chart kb).right_inv hV]
      rfl
    · show pRead M F keep (pBase M v φ) h (upV v φ) q.1.1.1 q.1.1.2.1 q.1.1.2.2 = w (ε (Sum.inr q))
      obtain ⟨hkeep, hpr, hbS, haS, hent⟩ := GlobalTheory.T.pMat_stepCols_entry Ψ N j keep q M.j_le
      obtain ⟨hval, hzero⟩ := hent (pL ε w)
      obtain ⟨k, hk⟩ : ∃ k, M.blk (q.1.1.1, pStep j keep q.1.1.1 q.1.1.2.2) = some k := by
        rcases e' : M.blk (q.1.1.1, pStep j keep q.1.1.1 q.1.1.2.2) with _ | k
        · exact absurd hpr ((M.blk_none _).1 e')
        · exact ⟨k, rfl⟩
      obtain ⟨hsgn, hsgn0⟩ := GlobalTheory.T.minorIJ_lowerUni_swap N (pMat keep (pL ε w) q.1.1.1)
        (stepCols N j (pStep j keep q.1.1.1 q.1.1.2.2)) q.1.1.2.1 q.1.1.2.2 (hL _) haS hbS q.1.2.1 hzero
      have e1 := hminor _ k hkeep hk
      rw [hbase]
      unfold pRead
      rw [hk]
      show twMinor M F (bl (pB ε w)) (pStep j keep q.1.1.1 q.1.1.2.2) k (h q.1.1.1)⁻¹ (upV v φ) _ /
        (_ * twMinor M F (bl (pB ε w)) (pStep j keep q.1.1.1 q.1.1.2.2) k (h q.1.1.1)⁻¹ (upV v φ) _) = _
      rw [e1, e1, hsgn, WMan.Read.minor_self_of_lowerUni (hL _), mul_one, mul_div_cancel_left₀ _ hsgn0, hval]
      rfl

end GlobalTheory.CompanionTheory.Ar.PB.PFl.ChartRead
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameDataLocalIntegrabilityStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameData_local_integrability : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ PIdx j keep ≃ Fin e), IsPCtx M Rb keep κ v F kb V bl r h → ∀ w ∈ pD ε V, pPhi M F keep v bl h ε w ∈ pO M Rb keep v F kb V r h ∧ pRho M Rb keep v F kb r h ε (pPhi M F keep v bl h ε w) = w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.PFl.ChartRead.chart_reads | exact GlobalTheory.CompanionTheory.Ar.PB.PFl.ChartRead.chart_reads | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.PFl.ChartRead.chart_reads <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentTwistedResolutionThird
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentTwistedResolutionThird
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FibNonempty

theorem anLogRes_W_nonempty : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)), Nonempty RW.X := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b k₀ ca cb hab hj hk hca hcb RW
  obtain ⟨x⟩ := flagAn_S_nonempty K ι Φ y Ψ N j M n d BM FA
  obtain ⟨l, hl⟩ := BM.O_cover (FA.pr x)
  have hz := GlobalTheory.T.flag_adjacent_arith_variety_first K ι Φ y Ψ N j M n BM d τ a b k₀ ca cb hab hj hk hca hcb FA.Re.arith l (FA.pr x) hl
    (fun _ => 1) 0 (fun _ => ⟨?_, by simp⟩)
  · obtain ⟨w, -⟩ := RW.surj _ hz (GlobalTheory.CompanionTheory.Ar.PB.Proj.not_mem_mcPts_top _)
    exact ⟨w⟩
  · intro r s hrs
    exact Matrix.one_apply_ne (fun e => hrs (by simp [e]))

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FibNonempty
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentTwistedResolutionThirdStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_twisted_resolution_third : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)), Nonempty RW.X := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FibNonempty.anLogRes_W_nonempty | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FibNonempty.anLogRes_W_nonempty | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FibNonempty.anLogRes_W_nonempty <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseMetricPullbackFamily
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsNullOfLocallyInZeros
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

namespace GlobalTheory.CompanionTheory.Ar.PB.NullLocal

theorem isNull_of_locally_in_zeros (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X)
    (Z : Set X)
    (hZ : ∀ x ∈ Z, ∃ (W : Set X) (f : X → ℂ), IsOpen W ∧ x ∈ W ∧ A.HoloOn W f ∧
      (∀ y ∈ W ∩ Z, f y = 0) ∧ ∀ V, IsOpen V → V.Nonempty → V ⊆ W → ∃ y ∈ V, f y ≠ 0) :
    IsNull A Z := by
  intro j
  refine measure_null_of_locally_null _ fun w hw => ?_
  obtain ⟨hwt, hwZ⟩ := hw
  obtain ⟨W, f, hWo, hxW, hf, hfZ, hne⟩ := hZ _ hwZ
  have hOo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' W) :=
    (A.chart j).isOpen_inter_preimage_symm hWo
  obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.mp hOo w ⟨hwt, hxW⟩
  have hV : IsOpen ((A.chart j).symm '' Metric.ball w r) :=
    (A.chart j).isOpen_image_symm_of_subset_target Metric.isOpen_ball
      fun z hz => (hrO hz).1
  obtain ⟨y, ⟨z, hz, rfl⟩, hy⟩ := hne _ hV ⟨_, w, Metric.mem_ball_self hr, rfl⟩ (by
    rintro _ ⟨z, hz, rfl⟩
    exact (hrO hz).2)
  have hnull := ReciprocityTheory.AnForm.volume_zero_set_of_analyticOnNhd (U := Metric.ball w r)
    Metric.isOpen_ball (convex_ball w r).isPreconnected
    (f := f ∘ (A.chart j).symm) ((hf j).mono hrO) ⟨z, hz, hy⟩
  refine ⟨((A.chart j).target ∩ (A.chart j).symm ⁻¹' Z) ∩ Metric.ball w r,
    inter_mem_nhdsWithin _ (Metric.ball_mem_nhds w hr), measure_mono_null ?_ hnull⟩
  rintro v ⟨⟨-, hvZ⟩, hvb⟩
  exact ⟨hvb, hfZ _ ⟨(hrO hvb).2, hvZ⟩⟩

end GlobalTheory.CompanionTheory.Ar.PB.NullLocal
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseMetricPullbackFamily
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

theorem section_eq_zero_iff {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {L : LocPot X}
    {s : X → X → ℂ} (hs : IsSection A L s) {b y : X} (hy : y ∈ L.U b) : s b y = 0 ↔ s y y = 0 := by
  have h := hs.2 b y y ⟨hy, L.mem_U y⟩
  have e1 := Real.exp_ne_zero (-L.φ b y)
  have e2 := Real.exp_ne_zero (-L.φ y y)
  constructor
  · intro h0
    rw [h0, norm_zero, zero_mul] at h
    exact norm_eq_zero.1 ((mul_eq_zero.1 h.symm).resolve_right e2)
  · intro h0
    rw [h0, norm_zero, zero_mul] at h
    exact norm_eq_zero.1 ((mul_eq_zero.1 h).resolve_right e1)

theorem isNull_off_bigCell : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (e : ℕ) (X' : Type) [TopologicalSpace X'] (A' : FinHolAtlas e X') (U' : X' → Set X') (lf : X' → X' → (Σ k, ι k) → ℂ) (pr' : X' → BM.Rb.X) (l : Fin BM.q), HoloMap A' BM.Rb.A pr' → (∀ x, IsOpen (U' x)) → (∀ x, x ∈ U' x) → (∀ x p, A'.HoloOn (U' x) (fun y => lf x y p)) → (∀ x, ∀ y ∈ U' x, SameOrbit (lf x y) (lf y y)) → (∀ x, pr' x ∈ BM.O l → ∀ V, IsOpen V → x ∈ V → ∃ x' ∈ V, pr' x' ∈ BM.O l \ bdry BM.s ∧ ∀ p, FC.plk M (BM.F l) (FC.bvec BM l (pr' x')) (lf x' x') p ≠ 0) → IsNull A' {x | pr' x ∈ BM.O l ∧ (pr' x ∈ bdry BM.s ∨ ∃ p, FC.plk M (BM.F l) (FC.bvec BM l (pr' x)) (lf x x) p = 0)} := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM e X' _ A' U' lf pr' l hpr hUo hUm hlf hor hden
  have hsec := BM.sec

  let f : X' → X' → ℂ := fun x w => BM.s (pr' x) (pr' w) *
    ∏ p : Ψ × Fin N, FC.plk M (BM.F l) (FC.bvec BM l (pr' w)) (lf x w) p
  let Wd : X' → Set X' := fun x => U' x ∩ pr' ⁻¹' (BM.O l ∩ BM.L.U (pr' x))
  have hWo : ∀ x, IsOpen (Wd x) := fun x =>
    (hUo x).inter (((BM.O_open l).inter (BM.L.isOpen_U _)).preimage hpr.1)

  have hne : ∀ x, ∀ w ∈ Wd x, pr' w ∉ bdry BM.s →
      (∀ p, FC.plk M (BM.F l) (FC.bvec BM l (pr' w)) (lf w w) p ≠ 0) → f x w ≠ 0 := by
    intro x w hw hb hp
    refine mul_ne_zero (fun h0 => hb ((section_eq_zero_iff hsec hw.2.2).1 h0)) ?_
    refine Finset.prod_ne_zero_iff.2 fun p _ => ?_
    exact (GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.plk_ne_zero_iff_of_sameOrbit K ι Φ y Ψ N j M (BM.F l) _ _ _ p (hor x w hw.1)).2 (hp p)

  have hholo : ∀ x, A'.HoloOn (Wd x) (f x) := by
    intro x
    have h1 : A'.HoloOn (Wd x) fun w => BM.s (pr' x) (pr' w) :=
      fun c => (GlobalTheory.CompanionTheory.Ar.PB.SncPull.holoOn_comp_pr hpr (hsec.1 (pr' x)) c).mono
        fun t ht => ⟨ht.1, ht.2.2.2⟩
    have h2 : ∀ p : Ψ × Fin N, A'.HoloOn (Wd x) fun w =>
        FC.plk M (BM.F l) (FC.bvec BM l (pr' w)) (lf x w) p := by
      intro p c
      have hV : IsOpen ((A'.chart c).target ∩ (A'.chart c).symm ⁻¹' Wd x) :=
        (A'.chart c).isOpen_inter_preimage_symm (hWo x)
      have hval := GlobalTheory.T.base_chart_holomorphic_composition K ι Φ y Ψ N j M n BM l e _ (pr' ∘ (A'.chart c).symm) hV
        (hpr.1.comp_continuousOn ((A'.chart c).continuousOn_symm.mono fun t ht => ht.1))
        (fun k => (hpr.2 c k).mono fun t ht => ⟨ht.1.1, ht.2⟩)
        (fun t ht => ht.2.2.1)
      have hreg : ∀ (q : Σ k, ι k) (I : Finset (Fin N)), ∀ b ∈ BM.O l,
          RegAt M.x (mCoordIdeal (FC.bvec BM l b)) ((BM.F l).u' I q) := fun q I b hb =>
        (((GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec_good K ι Φ y Ψ N j M n BM l b hb).2.1).2.1 q I).2
      unfold FC.plk
      rcases hb : M.blk p with _ | k
      · simpa [Function.comp_def] using analyticOnNhd_const
      · simp only [Option.elim]
        have : ∀ m : ι k, AnalyticOnNhd ℂ (fun t => valAt M.x ((BM.F l).u' (stepCols N j p.2) ⟨k, m⟩)
            (FC.bvec BM l ((pr' ∘ (A'.chart c).symm) t)) * lf x ((A'.chart c).symm t) ⟨k, m⟩)
            ((A'.chart c).target ∩ (A'.chart c).symm ⁻¹' Wd x) := fun m =>
          (hval.2 _ (hreg _ _)).mul (((hlf x ⟨k, m⟩) c).mono fun t ht => ⟨ht.1, ht.2.1⟩)
        intro t ht
        have := Finset.analyticAt_fun_sum Finset.univ fun m _ => this m t ht
        exact this
    refine FinHolAtlas.HoloOn.mul' h1 ?_
    intro c t ht
    exact Finset.analyticAt_fun_prod Finset.univ fun p _ => h2 p c t ht
  refine GlobalTheory.CompanionTheory.Ar.PB.NullLocal.isNull_of_locally_in_zeros e X' A' _ fun x hx => ⟨Wd x, f x, hWo x, ⟨hUm x, hx.1, BM.L.mem_U _⟩, hholo x, ?_, ?_⟩
  · rintro w ⟨hw, hwO, hwZ⟩
    rcases hwZ with hb | ⟨p, hp⟩
    · exact mul_eq_zero_of_left ((section_eq_zero_iff hsec hw.2.2).2 hb) _
    · refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ p) ?_)
      by_contra h0
      exact (GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.plk_ne_zero_iff_of_sameOrbit K ι Φ y Ψ N j M (BM.F l) _ _ _ p (hor x w hw.1)).1 h0 hp
  · rintro V hV ⟨x₁, hx₁⟩ hVW
    obtain ⟨x', hx'V, hx'b, hx'p⟩ := hden x₁ (hVW hx₁).2.1 V hV hx₁
    exact ⟨x', hx'V, hne x x' (hVW hx'V) hx'b.2 hx'p⟩

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseMetricPullbackFamilyStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_metric_pullback_family : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (e : ℕ) (X' : Type) [TopologicalSpace X'] (A' : FinHolAtlas e X') (U' : X' → Set X') (lf : X' → X' → (Σ k, ι k) → ℂ) (pr' : X' → BM.Rb.X) (l : Fin BM.q), HoloMap A' BM.Rb.A pr' → (∀ x, IsOpen (U' x)) → (∀ x, x ∈ U' x) → (∀ x p, A'.HoloOn (U' x) (fun y => lf x y p)) → (∀ x, ∀ y ∈ U' x, SameOrbit (lf x y) (lf y y)) → (∀ x, pr' x ∈ BM.O l → ∀ V, IsOpen V → x ∈ V → ∃ x' ∈ V, pr' x' ∈ BM.O l \ bdry BM.s ∧ ∀ p, FC.plk M (BM.F l) (FC.bvec BM l (pr' x')) (lf x' x') p ≠ 0) → IsNull A' {x | pr' x ∈ BM.O l ∧ (pr' x ∈ bdry BM.s ∨ ∃ p, FC.plk M (BM.F l) (FC.bvec BM l (pr' x)) (lf x x) p = 0)} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.isNull_off_bigCell | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.isNull_off_bigCell | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.isNull_off_bigCell <;> assumption)
end
end
