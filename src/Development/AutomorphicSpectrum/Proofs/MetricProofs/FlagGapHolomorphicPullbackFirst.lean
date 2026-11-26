module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsValueAtOfTorus
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HoloOnDivCongr

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapHolomorphicPullbackFirst
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapHolomorphicPullbackFirst
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CWeight

section Calc

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {N : ℕ}

def SmMat (M : E → Matrix (Fin N) (Fin N) ℂ) (w : E) : Prop :=
  ∀ a b, ContDiffAt ℝ ∞ (fun u => M u a b) w

theorem SmMat.mul {M M' : E → Matrix (Fin N) (Fin N) ℂ} {w : E} (h : SmMat M w) (h' : SmMat M' w) :
    SmMat (fun u => M u * M' u) w := by
  intro a b
  simp only [Matrix.mul_apply]
  exact ContDiffAt.sum fun c _ => (h a c).mul (h' c b)

theorem SmMat.conjTranspose {M : E → Matrix (Fin N) (Fin N) ℂ} {w : E} (h : SmMat M w) :
    SmMat (fun u => (M u)ᴴ) w := by
  intro a b
  simp only [Matrix.conjTranspose_apply]
  exact (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).contDiff.contDiffAt.comp w (h b a)

theorem SmMat.minor {M : E → Matrix (Fin N) (Fin N) ℂ} {w : E} (h : SmMat M w) (I J : Finset (Fin N)) :
    ContDiffAt ℝ ∞ (fun u => minorIJ (M u) I J) w := by
  unfold minorIJ
  by_cases e : I.card = J.card
  · simp only [dif_pos e, Matrix.det_apply']
    refine ContDiffAt.sum fun σ _ => contDiffAt_const.mul ?_
    exact contDiffAt_prod fun i _ => h _ _
  · simp only [dif_neg e]
    exact contDiffAt_const

theorem contDiffAt_blockPot (j : ℕ) (i : Fin N) {G h : E → Matrix (Fin N) (Fin N) ℂ} {w : E}
    (hG : SmMat G w) (hh : SmMat h w) (hpos : (G w).PosDef) (hdet : (h w).det ≠ 0) :
    ContDiffAt ℝ ∞ (fun u => blockPot j i (G u) (h u)) w := by
  have hre : ∀ {f : E → ℂ}, ContDiffAt ℝ ∞ f w → 0 < f w →
      ContDiffAt ℝ ∞ (fun u => Real.log (f u).re) w := fun hf h0 =>
    (Complex.reCLM.contDiff.contDiffAt.comp w hf).log (Complex.lt_def.1 h0).1.ne'
  have hfac : ContDiffAt ℝ ∞ (fun u => detFac j i (G u)) w := by
    unfold detFac
    refine ContDiffAt.mul ?_ ?_
    · by_cases c : j ≤ (i : ℕ) + 1
      · simpa only [if_pos c] using hG.minor _ _
      · simpa only [if_neg c] using contDiffAt_const
    · by_cases c : (i : ℕ) + 1 = N
      · simpa only [if_pos c] using hG.minor _ _
      · simpa only [if_neg c] using contDiffAt_const
  have hfac0 : 0 < detFac j i (G w) := by
    unfold detFac
    refine mul_pos ?_ ?_
    · split_ifs
      · exact GramPot.minor_pos hpos _
      · exact zero_lt_one
    · split_ifs
      · exact GramPot.minor_pos hpos _
      · exact zero_lt_one
  unfold blockPot
  refine (contDiffAt_const.mul (hre hfac hfac0)).add ?_
  by_cases c : IsProperStep N j i
  · simp only [if_pos c]
    refine contDiffAt_const.mul (hre ((hh.conjTranspose.mul hG).mul hh |>.minor _ _) ?_)
    have hu : IsUnit (h w) := (Matrix.isUnit_iff_isUnit_det _).2 hdet.isUnit
    exact GramPot.minor_pos
      (hpos.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hu)) _
  · simp only [if_neg c]
    exact contDiffAt_const

end Calc

section Chart

variable {e n : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem contDiffAt_comp_holoMap {A : FinHolAtlas e X} {B : FinHolAtlas n Y} {pr : X → Y}
    (hp : HoloMap A B pr) {U : Set Y} (hU : IsOpen U) {f : Y → ℝ} (hf : B.SmoothOn U f)
    (c : Fin A.n) {w : Fin e → ℂ} (hw : w ∈ (A.chart c).target)
    (hwU : pr ((A.chart c).symm w) ∈ U) :
    ContDiffAt ℝ ∞ (fun u => f (pr ((A.chart c).symm u))) w := by
  obtain ⟨k, hk⟩ := B.cover (pr ((A.chart c).symm w))
  have h1 : ContDiffAt ℝ ∞ (f ∘ (B.chart k).symm) (B.chart k (pr ((A.chart c).symm w))) := by
    refine (hf k).contDiffAt
      (((B.chart k).isOpen_inter_preimage_symm hU).mem_nhds ⟨(B.chart k).map_source hk, ?_⟩)
    simpa [(B.chart k).left_inv hk] using hwU
  have h2 : ContDiffAt ℝ ∞ (B.chart k ∘ pr ∘ (A.chart c).symm) w :=
    (hp.2 c k w ⟨hw, hk⟩).contDiffAt.restrict_scalars ℝ
  refine (ContDiffAt.comp w h1 h2).congr_of_eventuallyEq ?_
  filter_upwards [((A.chart c).isOpen_inter_preimage_symm
    ((B.chart k).open_source.preimage hp.1)).mem_nhds ⟨hw, hk⟩] with u hu
  simp only [Function.comp_apply, (B.chart k).left_inv hu.2]

theorem contDiffAt_of_re_im {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : E → ℂ} {w : E}
    (h1 : ContDiffAt ℝ ∞ (fun u => (g u).re) w) (h2 : ContDiffAt ℝ ∞ (fun u => (g u).im) w) :
    ContDiffAt ℝ ∞ g w := by
  have e : g = fun u => (((g u).re : ℝ) : ℂ) + (((g u).im : ℝ) : ℂ) * Complex.I := by
    funext u
    exact (Complex.re_add_im _).symm
  rw [e]
  exact (Complex.ofRealCLM.contDiff.contDiffAt.comp w h1).add
    ((Complex.ofRealCLM.contDiff.contDiffAt.comp w h2).mul contDiffAt_const)

end Chart

theorem smoothOn_stepPh : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr), HasStepCharts M BM p κ v R pr → IsPotential R.A (potOf R (fsHerm ιk fun k => M.dy p (κ k))) → R.A.SmoothOn (bdry (fun x y => BM.s (pr x) (pr y)))ᶜ (stepPh M BM p v R pr) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p Kk _ ιk _ κ v e R pr hp hS hP c w hw
  refine ContDiffAt.contDiffWithinAt ?_
  obtain ⟨hwt, hwb⟩ := hw
  have hb : pr ((R.A.chart c).symm w) ∉ bdry BM.s := hwb
  obtain ⟨W, l, H, D, hWo, hyW, hWU, hWO, hH, hHd, hD, hD0, heq⟩ :=
    hS ((R.A.chart c).symm w) ((R.A.chart c).symm w) (R.mem_U _)
  have hcl : IsClosed (bdry BM.s) := isClosed_bdry_of_isSection _ _ _ _ _ BM.sec
  have hOo : IsOpen (W ∩ pr ⁻¹' (bdry BM.s)ᶜ) := hWo.inter (hcl.isOpen_compl.preimage hp.1)
  have hnhd : (R.A.chart c).target ∩ (R.A.chart c).symm ⁻¹' (W ∩ pr ⁻¹' (bdry BM.s)ᶜ) ∈ 𝓝 w :=
    ((R.A.chart c).isOpen_inter_preimage_symm hOo).mem_nhds ⟨hwt, hyW, hb⟩
  have hOb : IsOpen (BM.O l \ bdry BM.s) := (BM.O_open l).sdiff hcl
  have hmemO : pr ((R.A.chart c).symm w) ∈ BM.O l \ bdry BM.s := ⟨hWO _ hyW, hb⟩
  have hG : SmMat (fun u => BM.G l p.1 (pr ((R.A.chart c).symm u))) w := fun a b =>
    contDiffAt_of_re_im
      (contDiffAt_comp_holoMap hp hOb (BM.G_smooth l p.1 a b).1 c hwt hmemO)
      (contDiffAt_comp_holoMap hp hOb (BM.G_smooth l p.1 a b).2 c hwt hmemO)
  have hHm : SmMat (fun u => H ((R.A.chart c).symm u)) w := fun a b =>
    (hH a b c w ⟨hwt, hyW⟩).contDiffAt.restrict_scalars ℝ
  have hDm : ContDiffAt ℝ ∞ (fun u => D ((R.A.chart c).symm u)) w :=
    (hD c w ⟨hwt, hyW⟩).contDiffAt.restrict_scalars ℝ
  have hD1 : D ((R.A.chart c).symm w) ≠ 0 := hD0 _ hyW
  have hbp := contDiffAt_blockPot j p.2 hG hHm (BM.G_pos l p.1 _ hmemO).2 (hHd _ hyW).2
  have hlog : ContDiffAt ℝ ∞ (fun u => Real.log ‖D ((R.A.chart c).symm u)‖) w :=
    (hDm.norm ℝ hD1).log (norm_ne_zero_iff.2 hD1)
  have hpot : ContDiffAt ℝ ∞ (fun u => Real.log ((fsHerm ιk fun k => M.dy p (κ k)).h
      (R.lift ((R.A.chart c).symm w) ((R.A.chart c).symm u)))) w :=
    (hP.1 ((R.A.chart c).symm w) c).contDiffAt
      (((R.A.chart c).isOpen_inter_preimage_symm (R.isOpen_U _)).mem_nhds ⟨hwt, R.mem_U _⟩)
  refine ((hbp.add hlog).sub hpot).congr_of_eventuallyEq ?_
  filter_upwards [hnhd] with u hu
  have := heq _ hu.2.1 hu.2.2
  simp only [Function.comp_apply]
  linarith

end GlobalTheory.CompanionTheory.Ar.PB.CWeight
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapHolomorphicPullbackFirstStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_gap_holomorphic_pullback_first : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr), HasStepCharts M BM p κ v R pr → IsPotential R.A (potOf R (fsHerm ιk fun k => M.dy p (κ k))) → R.A.SmoothOn (bdry (fun x y => BM.s (pr x) (pr y)))ᶜ (stepPh M BM p v R pr) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CWeight.smoothOn_stepPh | exact GlobalTheory.CompanionTheory.Ar.PB.CWeight.smoothOn_stepPh | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CWeight.smoothOn_stepPh <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartFirst
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartFirst
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Holo

section Gen

variable {e N : ℕ} {s : Set (Fin e → ℂ)}

theorem analytic_minorIJ (g : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (hg : ∀ a b, AnalyticOnNhd ℂ (fun w => g w a b) s) (I J : Finset (Fin N)) :
    AnalyticOnNhd ℂ (fun w => minorIJ (g w) I J) s := by
  by_cases e' : I.card = J.card
  · have hfun : (fun w => minorIJ (g w) I J) = fun w => ∑ σ : Equiv.Perm (Fin J.card),
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, g w (I.orderEmbOfFin e' (σ i)) (J.orderEmbOfFin rfl i) := by
      funext w
      rw [minorIJ, dite_eq_left e', Matrix.det_apply']
      rfl
    rw [hfun]
    have H := Finset.analyticOnNhd_sum (𝕜 := ℂ) (s := s) (Finset.univ : Finset (Equiv.Perm (Fin J.card)))
      (f := fun σ w => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, g w (I.orderEmbOfFin e' (σ i)) (J.orderEmbOfFin rfl i))
      (fun σ _ => analyticOnNhd_const.mul (by
        have P := Finset.analyticOnNhd_prod (𝕜 := ℂ) (s := s) (Finset.univ : Finset (Fin J.card))
          (f := fun i w => g w (I.orderEmbOfFin e' (σ i)) (J.orderEmbOfFin rfl i)) (fun i _ => hg _ _)
        convert P using 1
        funext w
        rw [Finset.prod_apply]))
    convert H using 1
    funext w
    rw [Finset.sum_apply]
  · have hfun : (fun w => minorIJ (g w) I J) = fun _ => 0 := by
      funext w
      rw [minorIJ, dite_eq_right e']
    rw [hfun]
    exact analyticOnNhd_const

theorem analytic_mul_entry (g g' : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (hg : ∀ a b, AnalyticOnNhd ℂ (fun w => g w a b) s)
    (hg' : ∀ a b, AnalyticOnNhd ℂ (fun w => g' w a b) s) (a b : Fin N) :
    AnalyticOnNhd ℂ (fun w => (g w * g' w) a b) s := by
  simp only [Matrix.mul_apply]
  have H := Finset.analyticOnNhd_sum (𝕜 := ℂ) (s := s) (Finset.univ : Finset (Fin N))
    (f := fun c w => g w a c * g' w c b) (fun c _ => (hg a c).mul (hg' c b))
  convert H using 1
  funext w
  rw [Finset.sum_apply]

theorem analytic_coord (i : Fin e) : AnalyticOnNhd ℂ (fun w : Fin e → ℂ => w i) s := by
  exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ) i).analyticOnNhd s

end Gen

section Flag

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} {n e : ℕ}

theorem analytic_lowMat (s : Set (Fin e → ℂ)) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin e) (τ' : Ψ) (a b : Fin N) :
    AnalyticOnNhd ℂ (fun w => lowMat (wL ε w) τ' a b) s := by
  by_cases hc : b < a ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)
  · have hfun : (fun w => lowMat (wL ε w) τ' a b) = fun w => w (ε (Sum.inr (Sum.inl ⟨(τ', a, b), hc⟩))) := by
      funext w
      simp only [lowMat]
      rw [dite_eq_left hc]
      rfl
    rw [hfun]
    exact analytic_coord _
  · have hfun : (fun w => lowMat (wL ε w) τ' a b) = fun _ => if a = b then (1 : ℂ) else 0 := by
      funext w
      simp only [lowMat]
      rw [dite_eq_right hc]
    rw [hfun]
    exact analyticOnNhd_const

theorem analytic_wH (s : Set (Fin e → ℂ)) (h : Ψ → Matrix (Fin N) (Fin N) ℂ)
    (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin e) (τ' : Ψ) (a b : Fin N) :
    AnalyticOnNhd ℂ (fun w => wH h ε τ' w a b) s := by
  exact analytic_mul_entry (s := s) (fun _ => h τ') (fun w => lowMat (wL ε w) τ') (fun _ _ => analyticOnNhd_const)
    (fun a b => analytic_lowMat s ε τ' a b) a b

theorem analytic_wH_snd (s : Set (Fin e → ℂ)) (h : Ψ → Matrix (Fin N) (Fin N) ℂ)
    (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin e) (τ : Ψ) (ca cb : Fin N) (a b : Fin N) :
    AnalyticOnNhd ℂ (fun w => (wH h ε τ w * (1 + Matrix.single cb ca (wT ε w))) a b) s := by
  refine analytic_mul_entry (s := s) (fun w => wH h ε τ w) (fun w => 1 + Matrix.single cb ca (wT ε w))
    (fun a b => analytic_wH s h ε τ a b) (fun a' b' => ?_) a b
  beta_reduce
  by_cases hc : cb = a' ∧ ca = b'
  · have hfun : (fun w => (1 + Matrix.single cb ca (wT ε w)) a' b') =
        fun w => (1 : Matrix (Fin N) (Fin N) ℂ) a' b' + w (ε (Sum.inr (Sum.inr ()))) := by
      funext w
      rw [Matrix.add_apply, Matrix.single_apply, if_pos hc]
      rfl
    rw [hfun]
    exact analyticOnNhd_const.add (analytic_coord _)
  · have hfun : (fun w => (1 + Matrix.single cb ca (wT ε w)) a' b') =
        fun _ => (1 : Matrix (Fin N) (Fin N) ℂ) a' b' + 0 := by
      funext w
      rw [Matrix.add_apply, Matrix.single_apply, if_neg hc]
    rw [hfun]
    exact analyticOnNhd_const

theorem analytic_flagZ (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) {s : Set (Fin e → ℂ)}
    (zb : (Fin e → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (H : (Fin e → ℂ) → Ψ → Matrix (Fin N) (Fin N) ℂ)
    (hzb : ∀ q, AnalyticOnNhd ℂ (fun w => zb w q) s)
    (hval : ∀ q I, AnalyticOnNhd ℂ (fun w => valAt M.x (F.u q I) (zb w)) s)
    (hH : ∀ τ' a b, AnalyticOnNhd ℂ (fun w => H w τ' a b) s) (q : Σ k, ι k) :
    AnalyticOnNhd ℂ (fun w => flagZ M F (zb w) (H w) q) s := by
  by_cases e' : ∃ p, M.blk p = some q.1
  · have hfun : (fun w => flagZ M F (zb w) (H w) q) = fun w =>
        ∑ I, valAt M.x (F.u q I) (zb w) * minorIJ (H w e'.choose.1) I (stepCols N j e'.choose.2) := by
      funext w
      simp only [flagZ]
      rw [dite_eq_left e']
    rw [hfun]
    have S := Finset.analyticOnNhd_sum (𝕜 := ℂ) (s := s) Finset.univ
      (f := fun I w => valAt M.x (F.u q I) (zb w) * minorIJ (H w e'.choose.1) I (stepCols N j e'.choose.2))
      (fun I _ => (hval q I).mul (analytic_minorIJ (fun w => H w e'.choose.1) (fun a b => hH _ a b) I _))
    convert S using 1
    funext w
    rw [Finset.sum_apply]
  · have hfun : (fun w => flagZ M F (zb w) (H w) q) = fun w => zb w ⟨⟨q.1, fun p hp => e' ⟨p, hp⟩⟩, q.2⟩ := by
      funext w
      simp only [flagZ]
      rw [dite_eq_right e']
    rw [hfun]
    exact hzb _

theorem analytic_wB {Λ : Type} (ε : Fin n ⊕ Λ ⊕ Unit ≃ Fin e) (V : Set (Fin n → ℂ)) :
    AnalyticOnNhd ℂ (wB ε) (wD ε V) := by
  exact AnalyticOnNhd.pi (fun i => analytic_coord (s := wD ε V) (ε (Sum.inl i)))

end Flag

theorem wPhi_holo : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ∀ p, AnalyticOnNhd ℂ (fun w => wPhi M F bl h ε k₀ τ ca cb w p) (wD ε V) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hctx p
  obtain ⟨-, -, -, -, -, -, -, ⟨-, -, hbl, hvl, -⟩, -, -, -⟩ := hctx
  have hB : AnalyticOnNhd ℂ (wB ε) (wD ε V) := analytic_wB ε V
  have hmaps : Set.MapsTo (wB ε) (wD ε V) V := fun w hw => hw
  have hzb : ∀ q, AnalyticOnNhd ℂ (fun w => bl (wB ε w) q) (wD ε V) := fun q => (hbl q).comp hB hmaps
  have hval : ∀ q I, AnalyticOnNhd ℂ (fun w => valAt M.x (F.u q I) (bl (wB ε w))) (wD ε V) :=
    fun q I => (hvl q I).comp hB hmaps
  obtain ⟨o, m⟩ := p
  cases o with
  | some k =>
    exact analytic_flagZ M F (fun w => bl (wB ε w)) (fun w τ' => wH h ε τ' w) hzb hval
      (fun τ' a' b' => analytic_wH _ h ε τ' a' b') ⟨k, m⟩
  | none =>
    refine analytic_flagZ M F (fun w => bl (wB ε w))
      (fun w => Function.update (fun τ' => wH h ε τ' w) τ (wH h ε τ w * (1 + Matrix.single cb ca (wT ε w))))
      hzb hval ?_ ⟨k₀, m⟩
    intro τ' a' b'
    by_cases hτ : τ' = τ
    · have hfun : (fun w => Function.update (fun τ'' => wH h ε τ'' w) τ
          (wH h ε τ w * (1 + Matrix.single cb ca (wT ε w))) τ' a' b') =
          fun w => (wH h ε τ w * (1 + Matrix.single cb ca (wT ε w))) a' b' := by
        funext w
        rw [Function.update_apply, if_pos hτ]
      rw [hfun]
      exact analytic_wH_snd _ h ε τ ca cb a' b'
    · have hfun : (fun w => Function.update (fun τ'' => wH h ε τ'' w) τ
          (wH h ε τ w * (1 + Matrix.single cb ca (wT ε w))) τ' a' b') = fun w => wH h ε τ' w a' b' := by
        funext w
        rw [Function.update_apply, if_neg hτ]
      rw [hfun]
      exact analytic_wH _ h ε τ' a' b'

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Holo
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartFirstStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_chart_first : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ∀ p, AnalyticOnNhd ℂ (fun w => wPhi M F bl h ε k₀ τ ca cb w p) (wD ε V) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.Holo.wPhi_holo | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.Holo.wPhi_holo | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.Holo.wPhi_holo <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothMinorOfSmoothMatrix
noncomputable section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.MinorSmooth

theorem contDiffOn_finsetProd {e : ℕ} {Un : Set (Fin e → ℂ)} {ι : Type} (s : Finset ι)
    (f : ι → (Fin e → ℂ) → ℂ)
    (h : ∀ i ∈ s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f i) Un) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => ∏ i ∈ s, f i w) Un := by
  induction s using Finset.induction_on with
  | empty => simpa using (contDiffOn_const : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : Fin e → ℂ => (1 : ℂ)) Un)
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem contDiffOn_det {e : ℕ} {Un : Set (Fin e → ℂ)} {σ : Type} [Fintype σ] [DecidableEq σ]
    (m : (Fin e → ℂ) → Matrix σ σ ℂ)
    (h : ∀ a b, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => m w a b) Un) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => (m w).det) Un := by
  have hdet : (fun w => (m w).det) =
      fun w => ∑ τ : Equiv.Perm σ, ((Equiv.Perm.sign τ : ℤ) : ℂ) * ∏ i, m w (τ i) i := by
    funext w
    exact Matrix.det_apply' _
  rw [hdet]
  exact ContDiffOn.sum fun τ _ => contDiffOn_const.mul
    (contDiffOn_finsetProd Finset.univ (fun i w => m w (τ i) i) fun i _ => h _ _)

theorem contDiffOn_minorIJ (N e : ℕ) (Un : Set (Fin e → ℂ))
    (A : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ) (I J : Finset (Fin N))
    (h : ∀ r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => A w r s) Un) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => minorIJ (A w) I J) Un := by
  by_cases hc : I.card = J.card
  · have hm : (fun w => minorIJ (A w) I J) =
        fun w => ((A w).submatrix (I.orderEmbOfFin hc) (J.orderEmbOfFin rfl)).det := by
      funext w
      rw [minorIJ, dite_eq_left hc]
    rw [hm]
    exact contDiffOn_det _ fun a b => h _ _
  · have hm : (fun w => minorIJ (A w) I J) = fun _ => (0 : ℂ) := by
      funext w
      rw [minorIJ, dite_eq_right hc]
    rw [hm]
    exact contDiffOn_const

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.MinorSmooth
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseChartFlagAnalyticMap
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothOnCompositionWithAnalyticMap
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem contDiffOn_comp_of_analytic_in_charts :
    ∀ (e n : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas n X) (Un : Set (Fin e → ℂ))
      (bp : (Fin e → ℂ) → X) (W : Set X) (f : X → ℝ), IsOpen Un → ContinuousOn bp Un →
      (∀ k, AnalyticOnNhd ℂ (A.chart k ∘ bp) (Un ∩ bp ⁻¹' (A.chart k).source)) →
      (∀ w ∈ Un, bp w ∈ W) → A.SmoothOn W f →
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f ∘ bp) Un := by
  intro e n X _ A Un bp W f hUn hbp hana hW hf w hw
  obtain ⟨k, hk⟩ := A.cover (bp w)
  have hV : IsOpen (Un ∩ bp ⁻¹' (A.chart k).source) :=
    hbp.isOpen_inter_preimage hUn (A.chart k).open_source
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (A.chart k ∘ bp) (Un ∩ bp ⁻¹' (A.chart k).source) :=
    ((hana k).contDiffOn hV.uniqueDiffOn).restrict_scalars ℝ
  have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f ∘ (A.chart k).symm)
      ((A.chart k).target ∩ (A.chart k).symm ⁻¹' W) := hf k
  have h3 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ((f ∘ (A.chart k).symm) ∘ (A.chart k ∘ bp))
      (Un ∩ bp ⁻¹' (A.chart k).source) := by
    refine h2.comp h1 ?_
    intro x hx
    refine ⟨(A.chart k).map_source hx.2, ?_⟩
    show (A.chart k).symm (A.chart k (bp x)) ∈ W
    rw [(A.chart k).left_inv hx.2]
    exact hW x hx.1
  have h4 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f ∘ bp) (Un ∩ bp ⁻¹' (A.chart k).source) := by
    refine h3.congr ?_
    intro x hx
    simp only [Function.comp_apply, (A.chart k).left_inv hx.2]
  exact (h4.contDiffAt (hV.mem_nhds ⟨hw, hk⟩)).contDiffWithinAt

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseChartFlagAnalyticMap
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem contDiffOn_gram_comp_basePoint :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n)  (l : Fin BM.q) (τ' : Ψ) (Un : Set (Fin d → ℂ)) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → ContinuousOn bp Un → (∀ k, AnalyticOnNhd ℂ (BM.Rb.A.chart k ∘ bp) (Un ∩ bp ⁻¹' (BM.Rb.A.chart k).source)) → (∀ w ∈ Un, bp w ∈ BM.O l \ bdry BM.s) → ∀ r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => BM.G l τ' (bp w) r s) Un := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM l τ' Un bp hU hbp han hmem r t
  have hre := contDiffOn_comp_of_analytic_in_charts _ _ _ BM.Rb.A Un bp _ _ hU hbp han hmem
    (BM.G_smooth l τ' r t).1
  have him := contDiffOn_comp_of_analytic_in_charts _ _ _ BM.Rb.A Un bp _ _ hU hbp han hmem
    (BM.G_smooth l τ' r t).2
  have h1 := Complex.ofRealCLM.contDiff.comp_contDiffOn hre
  have h2 := Complex.ofRealCLM.contDiff.comp_contDiffOn him
  have h3 := h1.add (h2.mul (contDiffOn_const (c := Complex.I)))
  refine h3.congr ?_
  intro w _
  simp [Complex.re_add_im]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseChartFlagAnalyticMapStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_chart_flag_analytic_map : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n)  (l : Fin BM.q) (τ' : Ψ) (Un : Set (Fin d → ℂ)) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → ContinuousOn bp Un → (∀ k, AnalyticOnNhd ℂ (BM.Rb.A.chart k ∘ bp) (Un ∩ bp ⁻¹' (BM.Rb.A.chart k).source)) → (∀ w ∈ Un, bp w ∈ BM.O l \ bdry BM.s) → ∀ r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => BM.G l τ' (bp w) r s) Un := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.contDiffOn_gram_comp_basePoint | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.contDiffOn_gram_comp_basePoint | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.contDiffOn_gram_comp_basePoint <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsUpperOfMinors
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.BigCell

theorem det_sub_congr {N : ℕ} (h : Matrix (Fin N) (Fin N) ℂ) (P Q : Fin N → Prop)
    [Fintype {a // P a}] [Fintype {a // Q a}] [DecidableEq {a // P a}] [DecidableEq {a // Q a}]
    (hPQ : ∀ a, P a ↔ Q a) :
    (h.submatrix (Subtype.val : {a // P a} → Fin N) Subtype.val).det =
      (h.submatrix (Subtype.val : {a // Q a} → Fin N) Subtype.val).det := by
  obtain rfl : P = Q := funext fun a => propext (hPQ a)
  congr!

theorem det_sub_eq_minorIJ {N : ℕ} (h : Matrix (Fin N) (Fin N) ℂ) (S : Finset (Fin N)) (P : Fin N → Prop)
    [Fintype {a // P a}] [DecidableEq {a // P a}] (hP : ∀ a, P a ↔ a ∈ S) :
    (h.submatrix (Subtype.val : {a // P a} → Fin N) Subtype.val).det = minorIJ h S S := by
  let e : Fin S.card ≃ {a // P a} :=
    (S.orderIsoOfFin rfl).toEquiv.trans (Equiv.subtypeEquivRight fun a => (hP a).symm)
  rw [minorIJ, dite_eq_left rfl, ← Matrix.det_submatrix_equiv_self e]
  congr 1

theorem exists_upper_of_minors : ∀ (N j : ℕ) (h : Matrix (Fin N) (Fin N) ℂ), j ≤ N → IsBlockDiag j h → h.det ≠ 0 → (∀ i : Fin N, IsProperStep N j i → minorIJ h (stepCols N j i) (stepCols N j i) ≠ 0) → ∃ B : Matrix (Fin N) (Fin N) ℂ, IsBlockDiag j B ∧ B.BlockTriangular id ∧ B.det ≠ 0 ∧ IsLowerUni (h * B) := by
  intro N j h hj hbd hdet hmin
  have hsplit := Matrix.twoBlockTriangular_det h (fun a : Fin N => (a : ℕ) < N - j)
    (fun a ha b hb => hbd a b fun e => ha (e.2 hb))
  rw [hsplit] at hdet
  have hA := left_ne_zero_of_mul hdet
  have hC := right_ne_zero_of_mul hdet
  have hu : ∀ b : Fin N, IsUnit (h.submatrix
      (Subtype.val : {a : Fin N // a ≤ b ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)} → Fin N) Subtype.val).det := by
    intro b
    rw [isUnit_iff_ne_zero]
    have hbN := b.isLt
    by_cases hb : (b : ℕ) < N - j
    · by_cases hl : (b : ℕ) + 1 = N - j
      · rw [det_sub_congr h _ (fun a : Fin N => (a : ℕ) < N - j) fun a => by
          simp only [Fin.le_def, hb, iff_true]; omega]
        exact hA
      · let i : Fin N := ⟨(b : ℕ) + j, by omega⟩
        have hi : (i : ℕ) = (b : ℕ) + j := rfl
        have hp : IsProperStep N j i := ⟨by omega, by omega⟩
        rw [det_sub_eq_minorIJ h (stepCols N j i) _ fun a => ?_]
        · exact hmin i hp
        · have : ¬ ((i : ℕ) + 1 ≤ j) := by omega
          simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg this, Fin.le_def, hb, iff_true]
          omega
    · by_cases hl : (b : ℕ) + 1 = N
      · rw [det_sub_congr h _ (fun a : Fin N => ¬ (a : ℕ) < N - j) fun a => by
          simp only [Fin.le_def, hb, iff_false]
          have := a.isLt
          omega]
        exact hC
      · let i : Fin N := ⟨(b : ℕ) - (N - j), by omega⟩
        have hi : (i : ℕ) = (b : ℕ) - (N - j) := rfl
        have hp : IsProperStep N j i := ⟨by omega, by omega⟩
        rw [det_sub_eq_minorIJ h (stepCols N j i) _ fun a => ?_]
        · exact hmin i hp
        · have : (i : ℕ) + 1 ≤ j := by omega
          simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos this, Fin.le_def, hb, iff_false]
          omega
  obtain ⟨B, h1, h2, h3⟩ := hbd.exists_upper hu
  refine ⟨B, h1, h2, fun hB => ?_, h3⟩
  have := h3.det
  rw [Matrix.det_mul, hB, mul_zero] at this
  exact zero_ne_one this

end GlobalTheory.CompanionTheory.Ar.PB.WSq.BigCell
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LowerUnipotentFamilyAnalytic
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LowerUnipotentFamilyAnalytic
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.LcFam

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem mul_elem_apply (A : Matrix (Fin N) (Fin N) ℂ) (ca cb r s : Fin N) (t : ℂ) :
    (A * (1 + Matrix.single cb ca t)) r s = A r s + if s = ca then A r cb * t else 0 := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
  congr 1
  rw [Matrix.mul_apply]
  by_cases h : s = ca
  · subst h
    simp [Matrix.single_apply]
  · simp [Matrix.single_apply, h, Ne.symm h]

theorem elem_mul_elem {ca cb : Fin N} (hne : ca ≠ cb) (t u : ℂ) :
    (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) * (1 + Matrix.single cb ca u) =
      1 + Matrix.single cb ca (t + u) := by
  ext r s
  rw [mul_elem_apply]
  by_cases h : s = ca
  · subst h
    by_cases hr : cb = r
    · subst hr
      simp [Matrix.add_apply, Matrix.single_apply, Matrix.one_apply, hne, Ne.symm hne]
      try ring
    · simp [Matrix.add_apply, Matrix.single_apply, Matrix.one_apply, hne, Ne.symm hne, hr, Ne.symm hr]
  · simp [Matrix.add_apply, Matrix.single_apply, h, Ne.symm h]

theorem mul_elem_cancel {ca cb : Fin N} (hne : ca ≠ cb) (A : Matrix (Fin N) (Fin N) ℂ) (t : ℂ) :
    A * (1 + Matrix.single cb ca t) * (1 + Matrix.single cb ca (-t)) = A := by
  rw [Matrix.mul_assoc, elem_mul_elem hne, add_neg_cancel, Matrix.single_zero, add_zero, Matrix.mul_one]

theorem isBlockDiag_elem {ca cb : Fin N} (hs : (cb : ℕ) < N - j ↔ (ca : ℕ) < N - j) (t : ℂ) :
    IsBlockDiag j (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) := by
  intro r s hrs
  have h1 : (1 : Matrix (Fin N) (Fin N) ℂ) r s = 0 := Matrix.one_apply_ne fun e => hrs (by rw [e])
  have h2 : (Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) r s = 0 := by
    rw [Matrix.single_apply, if_neg]
    rintro ⟨rfl, rfl⟩
    exact hrs hs
  rw [Matrix.add_apply, h1, h2, add_zero]

theorem isLowerUni_mul_elem {ca cb : Fin N} (hlt : ca < cb) {A : Matrix (Fin N) (Fin N) ℂ} (hA : IsLowerUni A)
    (t : ℂ) : IsLowerUni (A * (1 + Matrix.single cb ca t)) := by
  refine ⟨fun r => ?_, fun r s hrs => ?_⟩
  · rw [mul_elem_apply, hA.1]
    split_ifs with h
    · subst h
      rw [hA.2 r cb hlt, zero_mul, add_zero]
    · rw [add_zero]
  · rw [mul_elem_apply, hA.2 r s hrs]
    split_ifs with h
    · subst h
      rw [hA.2 r cb (hrs.trans hlt), zero_mul, add_zero]
    · rw [add_zero]

theorem isBlockDiag_Lc (τ : Ψ) (ca cb : Fin N) (c : FC.CIdx Ψ N j τ ca cb → ℂ) (τ' : Ψ) :
    IsBlockDiag j (FC.Lc τ ca cb c τ') := by
  intro r s hrs
  have hne : r ≠ s := fun e => hrs (by rw [e])
  unfold FC.Lc
  rw [dif_neg (fun h => hrs h.1.2), if_neg hne]

theorem isLowerUni_Lc (τ : Ψ) (ca cb : Fin N) (c : FC.CIdx Ψ N j τ ca cb → ℂ) (τ' : Ψ) :
    IsLowerUni (FC.Lc τ ca cb c τ') := by
  refine ⟨fun r => ?_, fun r s hrs => ?_⟩
  · unfold FC.Lc
    rw [dif_neg (fun h => lt_irrefl _ h.1.1), if_pos rfl]
  · unfold FC.Lc
    rw [dif_neg (fun h => lt_asymm hrs h.1.1), if_neg hrs.ne]

theorem Lc_apply_idx (τ : Ψ) (ca cb : Fin N) (c : FC.CIdx Ψ N j τ ca cb → ℂ) (q : FC.CIdx Ψ N j τ ca cb) :
    FC.Lc τ ca cb c q.1.1.1 q.1.1.2.1 q.1.1.2.2 = c q := by
  unfold FC.Lc
  rw [dif_pos (⟨q.1.2, q.2⟩ : _ ∧ _)]

theorem Lc_self_apply (τ : Ψ) {ca cb : Fin N} (hne : ca ≠ cb) (c : FC.CIdx Ψ N j τ ca cb → ℂ) :
    FC.Lc τ ca cb c τ cb ca = 0 := by
  unfold FC.Lc
  rw [dif_neg (fun h => h.2 rfl), if_neg (Ne.symm hne)]

theorem Lc_of_entries (τ : Ψ) {ca cb : Fin N} (hne : ca ≠ cb) (L : Ψ → Matrix (Fin N) (Fin N) ℂ)
    (hL : ∀ τ', IsBlockDiag j (L τ') ∧ IsLowerUni (L τ')) (h0 : L τ cb ca = 0) :
    FC.Lc τ ca cb (fun q : FC.CIdx Ψ N j τ ca cb => L q.1.1.1 q.1.1.2.1 q.1.1.2.2) = L := by
  funext τ'
  ext r s
  unfold FC.Lc
  split_ifs with h hrs
  · rfl
  · subst hrs
    exact ((hL τ').2.1 r).symm
  · by_cases e : (τ', r, s) = (τ, cb, ca)
    · obtain ⟨rfl, rfl, rfl⟩ : τ' = τ ∧ r = cb ∧ s = ca := by simpa using e
      exact h0.symm
    · have hn : ¬ (s < r ∧ ((r : ℕ) < N - j ↔ (s : ℕ) < N - j)) := fun h' => h ⟨h', e⟩
      by_cases hsr : s < r
      · exact ((hL τ').1 r s fun hb => hn ⟨hsr, hb⟩).symm
      · exact ((hL τ').2.2 r s (lt_of_le_of_ne (not_lt.1 hsr) hrs)).symm

theorem Lc_analytic (τ : Ψ) (ca cb : Fin N) (τ' : Ψ) (r s : Fin N) :
    AnalyticOnNhd ℂ (fun c : FC.CIdx Ψ N j τ ca cb → ℂ => FC.Lc τ ca cb c τ' r s) Set.univ := by
  unfold FC.Lc
  by_cases h : (s < r ∧ ((r : ℕ) < N - j ↔ (s : ℕ) < N - j)) ∧ (τ', r, s) ≠ (τ, cb, ca)
  · simp only [dif_pos h]
    exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : FC.CIdx Ψ N j τ ca cb => ℂ)
      ⟨⟨(τ', r, s), h.1⟩, h.2⟩).analyticOnNhd _
  · simp only [dif_neg h]
    exact analyticOnNhd_const

theorem exists_Lca (τ : Ψ) {ca cb : Fin N} (hlt : ca < cb) (hs : (cb : ℕ) < N - j ↔ (ca : ℕ) < N - j)
    (L : Ψ → Matrix (Fin N) (Fin N) ℂ) (hL : ∀ τ', IsBlockDiag j (L τ') ∧ IsLowerUni (L τ')) :
    ∃ (c : FC.CIdx Ψ N j τ ca cb → ℂ) (a : ℂ), FC.Lca τ ca cb c a = L := by
  have hne : ca ≠ cb := hlt.ne
  let a : ℂ := L τ cb ca
  let L' : Ψ → Matrix (Fin N) (Fin N) ℂ := Function.update L τ (L τ * (1 + Matrix.single cb ca (-a)))
  have hτ : L' τ = L τ * (1 + Matrix.single cb ca (-a)) := Function.update_self _ _ _
  have hL' : ∀ τ', IsBlockDiag j (L' τ') ∧ IsLowerUni (L' τ') := by
    intro τ'
    by_cases e : τ' = τ
    · subst e
      rw [hτ]
      exact ⟨(hL _).1.mul (isBlockDiag_elem hs _), isLowerUni_mul_elem hlt (hL _).2 _⟩
    · have : L' τ' = L τ' := Function.update_of_ne e _ _
      rw [this]
      exact hL τ'
  have h0 : L' τ cb ca = 0 := by
    rw [hτ, mul_elem_apply, if_pos rfl, (hL τ).2.1 cb, one_mul]
    exact add_neg_cancel _
  refine ⟨fun q => L' q.1.1.1 q.1.1.2.1 q.1.1.2.2, a, ?_⟩
  have hback : L τ * (1 + Matrix.single cb ca (-a)) * (1 + Matrix.single cb ca a) = L τ := by
    have := mul_elem_cancel hne (L τ) (-a)
    rwa [neg_neg] at this
  unfold FC.Lca
  rw [Lc_of_entries τ hne L' hL' h0, hτ, hback]
  funext τ'
  by_cases e : τ' = τ
  · subst e
    exact Function.update_self _ _ _
  · rw [Function.update_of_ne e]
    exact Function.update_of_ne e _ _

theorem Lca_prop (τ : Ψ) {ca cb : Fin N} (hlt : ca < cb) (hs : (cb : ℕ) < N - j ↔ (ca : ℕ) < N - j)
    (c : FC.CIdx Ψ N j τ ca cb → ℂ) (a : ℂ) (τ' : Ψ) :
    IsBlockDiag j (FC.Lca τ ca cb c a τ') ∧ IsLowerUni (FC.Lca τ ca cb c a τ') := by
  unfold FC.Lca
  by_cases e : τ' = τ
  · subst e
    rw [Function.update_self]
    exact ⟨(isBlockDiag_Lc _ _ _ _ _).mul (isBlockDiag_elem hs _), isLowerUni_mul_elem hlt (isLowerUni_Lc _ _ _ _ _) _⟩
  · rw [Function.update_of_ne e]
    exact ⟨isBlockDiag_Lc _ _ _ _ _, isLowerUni_Lc _ _ _ _ _⟩

theorem Lca_injective (τ : Ψ) {ca cb : Fin N} (hlt : ca < cb) (c c' : FC.CIdx Ψ N j τ ca cb → ℂ) (a a' : ℂ)
    (h : FC.Lca τ ca cb c a = FC.Lca τ ca cb c' a') : c = c' ∧ a = a' := by
  have hne : ca ≠ cb := hlt.ne
  have hτ : FC.Lc τ ca cb c τ * (1 + Matrix.single cb ca a) = FC.Lc τ ca cb c' τ * (1 + Matrix.single cb ca a') := by
    have := congrFun h τ
    unfold FC.Lca at this
    rwa [Function.update_self, Function.update_self] at this
  have entry : ∀ (d : FC.CIdx Ψ N j τ ca cb → ℂ) (t : ℂ),
      (FC.Lc τ ca cb d τ * (1 + Matrix.single cb ca t)) cb ca = t := fun d t => by
    rw [mul_elem_apply, if_pos rfl, Lc_self_apply τ hne, (isLowerUni_Lc τ ca cb d τ).1 cb, zero_add, one_mul]
  have ha : a = a' := by
    rw [← entry c a, hτ, entry]
  subst ha
  have hc : FC.Lc τ ca cb c = FC.Lc τ ca cb c' := by
    funext τ'
    by_cases e : τ' = τ
    · subst e
      rw [← mul_elem_cancel hne (FC.Lc τ' ca cb c τ') a, hτ, mul_elem_cancel hne]
    · have := congrFun h τ'
      unfold FC.Lca at this
      rwa [Function.update_of_ne e, Function.update_of_ne e] at this
  refine ⟨funext fun q => ?_, rfl⟩
  rw [← Lc_apply_idx τ ca cb c q, hc, Lc_apply_idx]

theorem lc_main : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (τ : Ψ) (ca cb : Fin N), ca < cb → ((cb : ℕ) < N - j ↔ (ca : ℕ) < N - j) → (∀ (c : FC.CIdx Ψ N j τ ca cb → ℂ) τ', IsBlockDiag j (FC.Lc τ ca cb c τ') ∧ (FC.Lc τ ca cb c τ').det ≠ 0) ∧ (∀ τ' r s, AnalyticOnNhd ℂ (fun c : FC.CIdx Ψ N j τ ca cb → ℂ => FC.Lc τ ca cb c τ' r s) Set.univ) ∧ (∀ L : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ', IsBlockDiag j (L τ') ∧ IsLowerUni (L τ')) → ∃ (c : FC.CIdx Ψ N j τ ca cb → ℂ) (a : ℂ), FC.Lca τ ca cb c a = L) ∧ (∀ (c : FC.CIdx Ψ N j τ ca cb → ℂ) (a : ℂ) τ', IsBlockDiag j (FC.Lca τ ca cb c a τ') ∧ IsLowerUni (FC.Lca τ ca cb c a τ')) ∧ ∀ (c c' : FC.CIdx Ψ N j τ ca cb → ℂ) (a a' : ℂ), FC.Lca τ ca cb c a = FC.Lca τ ca cb c' a' → c = c' ∧ a = a' := by
  intro Ψ _ _ N j τ ca cb hlt hs
  refine ⟨fun c τ' => ⟨isBlockDiag_Lc τ ca cb c τ', ?_⟩, fun τ' r s => Lc_analytic τ ca cb τ' r s,
    fun L hL => exists_Lca τ hlt hs L hL, fun c a τ' => Lca_prop τ hlt hs c a τ',
    fun c c' a a' h => Lca_injective τ hlt c c' a a' h⟩
  rw [(isLowerUni_Lc τ ca cb c τ').det]
  exact one_ne_zero

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.LcFam
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LowerUnipotentFamilyAnalyticStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lower_unipotent_family_analytic : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (τ : Ψ) (ca cb : Fin N), ca < cb → ((cb : ℕ) < N - j ↔ (ca : ℕ) < N - j) → (∀ (c : FC.CIdx Ψ N j τ ca cb → ℂ) τ', IsBlockDiag j (FC.Lc τ ca cb c τ') ∧ (FC.Lc τ ca cb c τ').det ≠ 0) ∧ (∀ τ' r s, AnalyticOnNhd ℂ (fun c : FC.CIdx Ψ N j τ ca cb → ℂ => FC.Lc τ ca cb c τ' r s) Set.univ) ∧ (∀ L : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ', IsBlockDiag j (L τ') ∧ IsLowerUni (L τ')) → ∃ (c : FC.CIdx Ψ N j τ ca cb → ℂ) (a : ℂ), FC.Lca τ ca cb c a = L) ∧ (∀ (c : FC.CIdx Ψ N j τ ca cb → ℂ) (a : ℂ) τ', IsBlockDiag j (FC.Lca τ ca cb c a τ') ∧ IsLowerUni (FC.Lca τ ca cb c a τ')) ∧ ∀ (c c' : FC.CIdx Ψ N j τ ca cb → ℂ) (a a' : ℂ), FC.Lca τ ca cb c a = FC.Lca τ ca cb c' a' → c = c' ∧ a = a' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.LcFam.lc_main | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.LcFam.lc_main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.LcFam.lc_main <;> assumption)
end
end
