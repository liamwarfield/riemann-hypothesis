module

public import Development.WeilBound.CoreStatements.CentralCharts.AnalyticAtEval
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEmbeddingOpenImmersion
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmTypeExteriorLatticeComparison
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagWeightedDegreeSection
public import Development.WeilBound.CoreStatements.CentralCharts.PshAt0LogNorm
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GlobalPairSumGramBound
public import Development.WeilBound.CoreStatements.CentralCharts.CommonMembers
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LowerBoundHeightOnBoundary

@[expose] public section

attribute [-instance] GlobalTheory.CompHt.fintypePsi

section -- merged from Development.WeilBound.CoreStatements.CentralCharts.ChartAnalytic
noncomputable section

namespace AnalyticReference.An

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open Filter Topology
open scoped ComplexOrder

theorem frame_sup {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {V : Type}
    [AddCommGroup V] [Module Ω V] (L : Lat ξ V) (W : Submodule Ω V) {r : ℕ} (bb : Fin r → W) (p : Cpt ξ)
    (hb : L.IsFrameAt (fun k => (bb k : V)) p) : (Lat.comap (fun p => L p ⊔ L p) W.subtype).IsFrameAt bb p := by
  have hspan : (Submodule.span (regAt ξ p) (Set.range bb)).map (W.subtype.restrictScalars (regAt ξ p)) =
      Submodule.span (regAt ξ p) (Set.range fun k => (bb k : V)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  refine ⟨LinearIndependent.of_comp W.subtype hb.1, ?_⟩
  ext x
  constructor
  · intro hx
    have h1 : (x : V) ∈ L p ⊔ L p := hx
    rw [sup_idem, hb.2, ← hspan] at h1
    obtain ⟨x', hx', e⟩ := h1
    have e' : x' = x := Subtype.ext e
    exact e' ▸ hx'
  · intro hx
    show (x : V) ∈ L p ⊔ L p
    rw [sup_idem, hb.2, ← hspan]
    exact ⟨x, hx, rfl⟩

theorem chart_analytic {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {P : Ideal (MRing J)} {n : ℕ}
    {Bd : Set ((Σ k, J k) → ℂ)} (χ : SncChart P n Bd) (q : Σ k, J k) : AnalyticAt ℂ (fun t => χ.γ t q) 0 :=
  ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, J k) => ℂ) q).analyticAt _).comp
    (χ.analytic 0 (Metric.mem_ball_self one_pos))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {Xo : ∀ l : Tor.Level H, Moduli D l} {l : Tor.Level H} {c : Coeff l} [NumberField c.F]
  {Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω : Type} [Field Ω] [CharZero Ω]
  {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

theorem label_data (hG : Top.Given) (hGl : Top.IsGlobal Xo l c Y) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) {n : ℕ}
    {Bd : Set ((Σ k, J k) → ℂ)}
    (hBd : ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ y z w → (w ∈ Bd ↔ ¬ 𝔐.Interior z))
    (χ : SncChart (mCoordIdeal y) n Bd) {z₀ : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X} (hz₀ : CoordsAt 𝔐.ξ y z₀ (χ.γ 0))
    (s : CMType H ⊕ CMType H) :
    ∃ (b : Fin (labelRk D s) → 𝔐.Li) (M : ℕ → (Fin n → ℂ) → ℝ),
      (∀ j, flagStep Ω b j = flagStep Ω (Fl.b s) j) ∧ (𝔐.V s).IsFrameAt b ⟨centre z₀, 𝔐.all _⟩ ∧
      (∀ t, M 0 t = 0) ∧ (∀ m ≤ labelRk D s, Tame χ.a (M m) ∧ (χ.a = 0 → PshAt0 (M m))) ∧
      ∀ᶠ t in 𝓝 (0 : Fin n → ℂ), (∀ i : Fin n, (i : ℕ) < χ.a → t i ≠ 0) →
        ∀ z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X, CoordsAt 𝔐.ξ y z (χ.γ t) → 𝔐.Interior z ∧
          (𝔐.V s).IsFrameAt b ⟨centre z, 𝔐.all _⟩ ∧ ∃ Γ, 𝔐.M.GramAt 𝔐.t.PP.L z b Γ ∧ Γ.PosDef ∧
            ∀ m ≤ labelRk D s, Real.log (leadMinor Γ m) = M m t := by
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := RingOfIntegers.coe_injective
  have hgen : genPt 𝔐.ξ ⤳ centre z₀ := 𝔐.all _
  obtain ⟨V, hV, b, hflag, hb⟩ := Fl.sub s ⟨centre z₀, hgen⟩ trivial
  have hb0 := hb ⟨centre z₀, hgen⟩ trivial hV
  obtain ⟨cc, f, hdom, -, hsub⟩ := exists_basic 𝔐.tie hz₀ hgen V hV
  obtain ⟨hVd, -, -⟩ := GlobalTheory.T.hodge_cpt_away_from_primes E H D l (Xo l) c _ _ Y S Ω K J y 𝔐 hβ ⟨centre z₀, hgen⟩
    fun r hr => GrNorm.not_inFibre 𝔐.tie.gen hgen hr
  have hmem : ∀ k, b k ∈ 𝔐.Vgen s ⊔ 𝔐.Vgen s := fun k => by
    have h1 : b k ∈ 𝔐.V s ⟨centre z₀, hgen⟩ := by
      rw [hb0.2]
      exact Submodule.subset_span ⟨k, rfl⟩
    rw [hVd s] at h1
    exact Submodule.mem_sup_left h1.2
  let bb : Fin (labelRk D s) → ↥(𝔐.Vgen s ⊔ 𝔐.Vgen s) := fun k => ⟨b k, hmem k⟩
  obtain ⟨a₀, g, Λ, _, L, π, ρ, U, hρ, hρ1, hU, hli, ha, hP⟩ :=
    GlobalTheory.T.global_pair_sum_gram_bound hG E H D Xo l c Y S Ω K J y 𝔐 hGl s s _ bb n Bd χ 0 cc f hBd (Metric.mem_ball_self one_pos)
      (fun p h1 h2 => frame_sup (𝔐.V s) _ bb p (hb p trivial (hsub p h1 h2))) hdom
  let M : ℕ → (Fin n → ℂ) → ℝ := fun m t =>
    Real.log (leadMinor (HodgeMetric.periodGram L U (HodgeMetric.uncentre 0 ρ π t)) m)
  have hM : ∀ m (h : m ≤ labelRk D s), M m = fun t => Real.log
      (HodgeMetric.periodGram L (fun j => U (Fin.castLE h j)) (HodgeMetric.uncentre 0 ρ π t)).det.re := by
    intro m h
    funext t
    simp only [M, leadMinor, dif_pos h]
    rfl
  refine ⟨b, M, hflag, hb0, fun t => by simp [M, leadMinor_size_zero], fun m hm => ?_, ?_⟩
  · rw [hM m hm]
    have hli' : LinearIndependent ℂ fun j : Fin m => U (Fin.castLE hm j) 0 := hli.comp _ (Fin.castLE_injective hm)
    refine ⟨tame_logdet L _ π ρ hρ hρ1 (fun j => hU _) hli' fun i hi => (ha i hi).1, fun h0 => ?_⟩
    have : a₀ = 0 := by
      by_contra hne
      have hle := L.a_le
      have := (ha ⟨0, by omega⟩ (Nat.pos_of_ne_zero hne)).1
      omega
    subst this
    exact pshAt0_logdet L _ π ρ hρ (fun j => hU _) hli'
  · filter_upwards [Metric.ball_mem_nhds (0 : Fin n → ℂ) hρ] with t ht hoff z hz
    have hu := HodgeMetric.uncentre_mem_ball (t₀ := 0) (t := t) hρ π (by simpa using ht)
    obtain ⟨h1, h2, h3, h4⟩ := hP _ hu
    rw [HodgeMetric.recentre_uncentre 0 hρ π t] at h1 h2 h3 h4
    have hnb : χ.γ t ∉ Bd := fun h => by
      obtain ⟨i, hi, h0⟩ := (χ.boundary t h1).1 h
      exact hoff i hi h0
    have hi : 𝔐.Interior z := by_contra fun h => hnb ((hBd z _ hz).2 h)
    have hc := GlobalTheory.T.frame_domain_in_segre_chart 𝔐.X Ω 𝔐.ξ K J y 𝔐.tie z _ cc f (𝔐.all _) hz h2
    have hfr := hb _ trivial (hsub _ hc.1 hc.2)
    have hΓ := h4 (h3.1 hnb) z hz
    obtain ⟨Γ, g1, g2⟩ := RootGram.exists_gram 𝔐 hi s hfr
    have e := GlobalTheory.T.gram_matrix_change_frame E H D l (Xo l) c Y S Ω K J y 𝔐 z _ b _ _
      (GlobalTheory.T.interior_point_polarised E H D l (Xo l) c Y S Ω K J y 𝔐 z hi) g1 hΓ
    refine ⟨hi, hfr, Γ, g1, g2, fun m _ => ?_⟩
    rw [e]

theorem root_data (hG : Top.Given) (hGl : Top.IsGlobal Xo l c Y) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) {n : ℕ}
    {Bd : Set ((Σ k, J k) → ℂ)}
    (hBd : ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ y z w → (w ∈ Bd ↔ ¬ 𝔐.Interior z))
    (χ : SncChart (mCoordIdeal y) n Bd) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ)
    (e : CMType H × Fin (D.p + D.q) → Ω) (hx : CMType H × Fin (D.p + D.q) → HermLine J) (hroot : Fl.RootLines xdeg e)
    (hhod : ∀ r, Fl.IsHodgeLine r (e r) (hx r)) (hdg : ∀ r, (hx r).a = xdeg r) :
    ∃ (M : CMType H ⊕ CMType H → ℕ → (Fin n → ℂ) → ℝ) (F : CMType H × Fin (D.p + D.q) → (Fin n → ℂ) → ℂ),
      (∀ s t, M s 0 t = 0) ∧ (∀ s, ∀ m ≤ labelRk D s, Tame χ.a (M s m) ∧ (χ.a = 0 → PshAt0 (M s m))) ∧
      (∀ r, AnalyticAt ℂ (F r) 0 ∧ F r 0 ≠ 0) ∧
      ∀ r, ∀ᶠ t in 𝓝 (0 : Fin n → ℂ), (∀ i : Fin n, (i : ℕ) < χ.a → t i ≠ 0) →
        Real.log ((hx r).h (χ.γ t)) = Real.log ‖F r t‖ - (HodgeCpt.rootSgn D r : ℝ) / 2 *
          (M (HodgeCpt.rootIdx D r).1 (((HodgeCpt.rootIdx D r).2 : ℕ) + 1) t -
            M (HodgeCpt.rootIdx D r).1 ((HodgeCpt.rootIdx D r).2 : ℕ) t) := by
  have pts : ∀ w ∈ mcPts (mCoordIdeal y), ∃ z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X, CoordsAt 𝔐.ξ y z w := fun w hw => by
    obtain ⟨z, -, hz⟩ := (GlobalTheory.T.complex_points_iff_centres 𝔐.X Ω 𝔐.ξ K J y 𝔐.tie w).1 hw
    exact ⟨z, hz⟩
  obtain ⟨z₀, hz₀⟩ := pts _ (χ.mem 0 (Metric.mem_ball_self one_pos))
  have hgen : genPt 𝔐.ξ ⤳ centre z₀ := 𝔐.all _
  choose b M hflag hb0 hM0 hM hev using label_data hG hGl 𝔐 Fl hBd χ hz₀
  obtain ⟨cc, f, hdom, hch, -⟩ := exists_basic 𝔐.tie hz₀ hgen ⊤ trivial
  have hcc : ∀ᶠ t in 𝓝 (0 : Fin n → ℂ), ∀ k, χ.γ t ⟨k, cc k⟩ ≠ 0 :=
    eventually_all.2 fun k => (chart_analytic χ _).continuousAt.eventually_ne (hdom.1 k)
  have key : ∀ r : CMType H × Fin (D.p + D.q), ∃ F : (Fin n → ℂ) → ℂ, (AnalyticAt ℂ F 0 ∧ F 0 ≠ 0) ∧
      ∀ᶠ t in 𝓝 (0 : Fin n → ℂ), (∀ i : Fin n, (i : ℕ) < χ.a → t i ≠ 0) →
        Real.log ((hx r).h (χ.γ t)) = Real.log ‖F t‖ - (HodgeCpt.rootSgn D r : ℝ) / 2 *
          (M (HodgeCpt.rootIdx D r).1 (((HodgeCpt.rootIdx D r).2 : ℕ) + 1) t -
            M (HodgeCpt.rootIdx D r).1 ((HodgeCpt.rootIdx D r).2 : ℕ) t) := by
    intro r
    obtain ⟨τ, hτ⟩ := GrNorm.exists_sub_mem_flagStep (b := Fl.b (HodgeCpt.rootIdx D r).1) (HodgeCpt.rootIdx D r).2
      (x := b _ (HodgeCpt.rootIdx D r).2) (by
        rw [← hflag]
        exact Submodule.subset_span ⟨_, Nat.lt_succ_self _, rfl⟩)
    have hu := GlobalTheory.T.root_lines_flag_degree E H D l (Xo l) c Y S Ω K J y 𝔐 Fl xdeg e r _ cc _ τ hroot hch (hflag _) (hb0 _) hτ
    obtain ⟨v, hv0, hv⟩ := exists_val_ne hgen hu
    have hv' := CxVal.inv hv hv0
    rw [inv_div] at hv'
    obtain ⟨F₁, hF₁, hF0, hF⟩ := exists_val_fam 𝔐.tie 𝔐.all (chart_analytic χ) hz₀ hv'
    have hne : F₁ 0 * ∏ k, χ.γ 0 ⟨k, cc k⟩ ^ xdeg r k ≠ 0 :=
      mul_ne_zero (by rw [hF0]; exact inv_ne_zero hv0)
        (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hdom.1 k))
    refine ⟨fun t => F₁ t * ∏ k, χ.γ t ⟨k, cc k⟩ ^ xdeg r k, ⟨hF₁.fun_mul
      (Finset.analyticAt_fun_prod _ fun k _ => (chart_analytic χ _).fun_zpow (hdom.1 k)), hne⟩, ?_⟩
    filter_upwards [hev (HodgeCpt.rootIdx D r).1, hF, hcc, Metric.ball_mem_nhds (0 : Fin n → ℂ) one_pos] with
      t h1 h2 h3 h4 hoff
    obtain ⟨z, hz⟩ := pts _ (χ.mem t h4)
    obtain ⟨hi, hfr, Γ, g1, g2, g3⟩ := h1 hoff z hz
    have hN := hhod r z _ hz hi τ _ ⟨𝔐.all _, _, Γ, hflag _, hfr, hτ, g1, g2, rfl⟩
    obtain ⟨u, hu1, hu2⟩ := hN.2.2 cc h3
    rw [hdg] at hu1 hu2
    rw [CxVal.unique hu1 (h2 z hz)] at hu2
    have p1 := leadMinor_pos_of_posDef g2 (s := ((HodgeCpt.rootIdx D r).2 : ℕ) + 1) (HodgeCpt.rootIdx D r).2.2
    have p2 := leadMinor_pos_of_posDef g2 (s := ((HodgeCpt.rootIdx D r).2 : ℕ)) (HodgeCpt.rootIdx D r).2.2.le
    have p3 : 0 < (hx r).h (χ.γ t) := (hx r).pos _ fun k => ⟨cc k, h3 k⟩
    have e1 := congrArg Real.log hu2
    rw [Real.log_mul (zpow_ne_zero _ (Real.sqrt_pos.2 (div_pos p1 p2)).ne') p3.ne', Real.log_zpow,
      Real.log_sqrt (div_pos p1 p2).le, Real.log_div p1.ne' p2.ne', g3 _ (HodgeCpt.rootIdx D r).2.2,
      g3 _ (HodgeCpt.rootIdx D r).2.2.le] at e1
    simp only [norm_mul, norm_prod, norm_zpow]
    rw [← e1]
    ring
  choose F hF hF' using key
  exact ⟨M, F, hM0, hM, hF, hF'⟩

end AnalyticReference.An
end
end

section -- merged from Development.WeilBound.CoreStatements.CentralCharts.OneLeDimFl
section -- merged from Development.WeilBound.CoreStatements.CentralCharts.IsPosPotBlock
noncomputable section

namespace AnalyticReference.An

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo Filter Topology Metric
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.PB

variable {n : ℕ} {K : Type} [Fintype K] [DecidableEq K] {J : K → Type} [∀ k, Fintype (J k)] {P : Ideal (MRing J)}

theorem fs_single_h (k₀ : K) (z : (Σ k, J k) → ℂ) :
    (fsHerm J (Pi.single k₀ 1)).h z = Real.sqrt (∑ i, ‖z ⟨k₀, i⟩‖ ^ 2) := by
  show refNorm (Pi.single k₀ 1) z = _
  unfold refNorm
  rw [Finset.prod_eq_single k₀]
  · simp [Real.sqrt_eq_rpow]
  · intro k _ hk
    simp [Pi.single_apply, hk]
  · intro h
    exact absurd (Finset.mem_univ k₀) h

private theorem fsHerm_unit_h_eq_sqrt_sum_sq {ι : Type} [Fintype ι] (u : (Σ _ : Unit, ι) → ℂ) :
    (fsHerm (fun _ : Unit => ι) fun _ => 1).h u = Real.sqrt (∑ i, ‖u ⟨(), i⟩‖ ^ 2) := by
  rw [fsHerm_h]
  simp [refNorm, Real.sqrt_eq_rpow]

private theorem differentiableAt_div_coord_of_ne_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {Q : Type} [Fintype Q]
    {τ : E → Q → ℂ} {y : E} (hτd : DifferentiableAt ℂ τ y) (q₀ : Q) (h0 : τ y q₀ ≠ 0) :
    DifferentiableAt ℂ (fun v q => τ v q / τ v q₀) y := by
  rw [differentiableAt_pi]
  intro q
  have hq : DifferentiableAt ℂ (fun v => τ v q) y := (differentiableAt_pi.1 hτd) q
  have h₀ : DifferentiableAt ℂ (fun v => τ v q₀) y := (differentiableAt_pi.1 hτd) q₀
  simp only [div_eq_mul_inv]
  exact hq.fun_mul (h₀.fun_inv h0)

theorem isPosPot_block (R : AnLogRes P ⊤ n) (k₀ : K)
    (himm : ∀ (x : R.X) (p : J k₀), R.lift x x ⟨k₀, p⟩ ≠ 0 → ∀ j, x ∈ (R.A.chart j).source →
      (fderiv ℂ (fun (v : Fin n → ℂ) (i : J k₀) => R.lift x ((R.A.chart j).symm v) ⟨k₀, i⟩ /
        R.lift x ((R.A.chart j).symm v) ⟨k₀, p⟩) (R.A.chart j x)).ker = ⊥) :
    IsPosPot R.A (potOf R (fsHerm J (Pi.single k₀ 1))) := by
  intro x j y hy w hw
  obtain ⟨hyt, hyU⟩ := hy
  let τ : (Fin n → ℂ) → (Σ _ : Unit, J k₀) → ℂ :=
    fun v q => R.lift x ((R.A.chart j).symm v) ⟨k₀, q.2⟩
  let ψ : ((Σ _ : Unit, J k₀) → ℂ) → ℝ :=
    fun u => Real.log ((fsHerm (fun _ : Unit => J k₀) fun _ => 1).h u)
  have hfun : (potOf R (fsHerm J (Pi.single k₀ 1))).φ x ∘ (R.A.chart j).symm = ψ ∘ τ := by
    funext v
    simp only [Function.comp, potOf, ψ, τ]
    rw [fs_single_h, fsHerm_unit_h_eq_sqrt_sum_sq]
  rw [hfun]
  have hmem := R.mem x _ hyU
  obtain ⟨p, hp⟩ := hmem.1 k₀
  have hτan : AnalyticAt ℂ τ y := by
    rw [analyticAt_pi_iff]
    intro q
    exact R.holo x ⟨k₀, q.2⟩ j y ⟨hyt, hyU⟩
  have hτne : ∀ k : Unit, ∃ i, τ y ⟨k, i⟩ ≠ 0 := fun _ => ⟨p, hp⟩
  have hsm : ContDiffAt ℝ 2 ψ (τ y) :=
    GlobalTheory.CompanionTheory.Ar.PB.PosFs.contDiffAt_log_h (GlobalTheory.CompanionTheory.Ar.PB.StepW.fsHerm_isSmoothHerm _ _ _) hτne
  rw [levi_comp w hτan hsm]
  apply GlobalTheory.CompanionTheory.Ar.PB.PosFs.levi_fs_pos hτne
  intro c hc
  apply hw
  set y' := (R.A.chart j).symm y with hy'eq
  have hy'src : y' ∈ (R.A.chart j).source := (R.A.chart j).map_target hyt
  have hcy : (R.A.chart j) y' = y := (R.A.chart j).right_inv hyt
  have hUy' : y' ∈ R.U y' := R.mem_U y'
  obtain ⟨c', hc'ne, hc'eq⟩ := R.compat x y' y' ⟨hyU, hUy'⟩
  have hp' : R.lift y' y' ⟨k₀, p⟩ ≠ 0 := by
    intro h
    apply hp
    show R.lift x y' ⟨k₀, p⟩ = 0
    rw [hc'eq]
    simp [h]
  have hker := himm y' p hp' j hy'src
  rw [hcy] at hker
  let ρ : (Fin n → ℂ) → J k₀ → ℂ := fun v i =>
    R.lift x ((R.A.chart j).symm v) ⟨k₀, i⟩ / R.lift x ((R.A.chart j).symm v) ⟨k₀, p⟩
  have hev : (fun (v : Fin n → ℂ) (i : J k₀) => R.lift y' ((R.A.chart j).symm v) ⟨k₀, i⟩ /
      R.lift y' ((R.A.chart j).symm v) ⟨k₀, p⟩) =ᶠ[𝓝 y] ρ := by
    have hcont := (R.A.chart j).continuousAt_symm hyt
    have hnb : (R.A.chart j).symm ⁻¹' (R.U x ∩ R.U y') ∈ 𝓝 y :=
      hcont.preimage_mem_nhds (((R.isOpen_U x).inter (R.isOpen_U y')).mem_nhds ⟨hyU, hUy'⟩)
    filter_upwards [hnb] with v hv
    obtain ⟨d, hdne, hdeq⟩ := R.compat x y' _ hv
    funext i
    simp only [ρ, hdeq]
    rw [mul_div_mul_left _ _ (hdne k₀)]
  have hτd : DifferentiableAt ℂ τ y := hτan.differentiableAt
  let g : (Fin n → ℂ) → (Σ _ : Unit, J k₀) → ℂ := fun v => affCoord (fun _ : Unit => p) (τ v)
  have hg0 : fderiv ℂ g y w = 0 :=
    GlobalTheory.CompanionTheory.Ar.PB.PosFs.fderiv_affCoord_torus (fun _ : Unit => p) hτd (fun _ => hp) hc
  have hgd : DifferentiableAt ℂ g y := differentiableAt_div_coord_of_ne_zero hτd ⟨(), p⟩ hp
  let L : ((Σ _ : Unit, J k₀) → ℂ) →L[ℂ] (J k₀ → ℂ) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (⟨(), i⟩ : Σ _ : Unit, J k₀)
  have hρ : ρ = L ∘ g := rfl
  have hρ0 : fderiv ℂ ρ y w = 0 := by
    rw [hρ, fderiv_comp y L.differentiableAt hgd, L.fderiv]
    simp [hg0]
  have hmk : w ∈ LinearMap.ker (fderiv ℂ (fun (v : Fin n → ℂ) (i : J k₀) =>
      R.lift y' ((R.A.chart j).symm v) ⟨k₀, i⟩ / R.lift y' ((R.A.chart j).symm v) ⟨k₀, p⟩) y :
        (Fin n → ℂ) →ₗ[ℂ] (J k₀ → ℂ)) := by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hev.fderiv_eq]
    exact hρ0
  rw [hker] at hmk
  exact (Submodule.mem_bot ℂ).1 hmk

end AnalyticReference.An
end
end

noncomputable section

namespace AnalyticReference.An

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB Filter Topology Metric

theorem weight_orbit {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {σ : Type} (S : Finset σ)
    (A : σ → HermLine J) {z z' : (Σ k, J k) → ℂ} (hz : ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0) (h : SameOrbit z z') :
    -∑ k ∈ S, Real.log ((A k).h z) - Real.log ((fsHerm J (-∑ k ∈ S, (A k).a)).h z) =
      -∑ k ∈ S, Real.log ((A k).h z') - Real.log ((fsHerm J (-∑ k ∈ S, (A k).a)).h z') := by
  obtain ⟨c, hc, rfl⟩ := h
  have e : ∀ B : HermLine J, Real.log (B.h fun p => c p.1 * z' p) =
      ∑ k, (B.a k : ℝ) * Real.log ‖c k‖ + Real.log (B.h z') := fun B => by
    rw [B.smul c z' hc, Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k)))
      (B.pos z' hz).ne', Real.log_prod fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))]
    simp only [Real.log_zpow]
  simp only [e, Finset.sum_add_distrib]
  have : ∑ k, (((fsHerm J (-∑ k ∈ S, (A k).a)).a k : ℤ) : ℝ) * Real.log ‖c k‖ =
      -∑ j ∈ S, ∑ k, ((A j).a k : ℝ) * Real.log ‖c k‖ := by
    have e2 : ∀ k, (fsHerm J (-∑ j ∈ S, (A j).a)).a k = -∑ j ∈ S, (A j).a k := fun k => by
      show (-∑ j ∈ S, (A j).a : K → ℤ) k = _
      simp [Finset.sum_apply]
    simp only [e2]
    rw [Finset.sum_comm]
    simp [Finset.sum_mul]
  rw [this]
  ring

theorem one_le_dimFl {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {N : ℕ} (hN : 2 ≤ N) :
    1 ≤ Top.dimFl (CMType H) N := by
  have h1 : Fintype.card (CMType H) = Module.finrank ℚ E / 2 := by
    rw [Fintype.card_eq_nat_card]; exact GlobalTheory.PeriodCoord.card_cmType H
  have h2 : 2 ≤ Module.finrank ℚ E := by
    have := IsTotallyComplex.finrank E
    have h0 : 0 < Module.finrank ℚ E := Module.finrank_pos
    omega
  have h3 : 2 * 1 ≤ N * (N - 1) := Nat.mul_le_mul hN (by omega)
  unfold Top.dimFl
  exact Nat.mul_pos (by omega) (by omega)

theorem of_local (hI : PB.Inputs) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Tor.Level H} {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)}
    (hp : 1 ≤ D.p) (hq : 1 ≤ D.q) (G : RefGeo Y) (sing : RootIx D → HermLine G.J)
    (hdeg : ∀ r, (sing r).a = G.xdeg r) (hhodge : ∀ r, G.Fl.IsHodgeLine r (G.e r) (sing r))
    (hconj : ∀ r, IsConjInvariantH (sing r))
    (hloc : ∀ (χ : SncChart (mCoordIdeal G.y) (Top.dimFl (CMType H) (D.p + D.q)) (mcPts G.bd)) (τ : CMType H)
      (i : Fin (D.p + D.q)),
      Tame χ.a (fun t => -∑ k ∈ Finset.Iic i, Real.log ((sing (τ, k)).h (χ.γ t))) ∧
      (χ.a = 0 → PshAt0 (fun t => -∑ k ∈ Finset.Iic i, Real.log ((sing (τ, k)).h (χ.γ t))) ∧
        ((i : ℕ) + 1 = D.p + D.q → PshAt0 fun t => ∑ k ∈ Finset.Iic i, Real.log ((sing (τ, k)).h (χ.γ t))))) :
    ∃ A : G.An, (∃ inv : A.Sys.X → A.Re.R.X, ReciprocityTheory.AnForm.M.HoloMap A.Sys.A A.Re.R.A inv ∧
      ∀ x, inv (A.Re.π x) = x) := by
  classical
  have harith := GlobalTheory.T.isArithVar_of_snc_model G.𝔐.X G.Ω G.𝔐.ξ G.K G.J G.y _ G.bd (one_le_dimFl H (N := D.p + D.q) (by omega)) G.𝔐.tie G.snc
  obtain ⟨y1, y2, y3⟩ := GlobalTheory.T.boundary_points_closed G.𝔐.X G.Ω G.𝔐.ξ G.K G.J G.y (abLocus G.𝔐.t.G) G.bd G.𝔐.tie G.bd_iff
  obtain ⟨R, L, s, nb, m, W, hL, hs, snc, hn, hbd, hrc⟩ := GlobalTheory.T.lowerBound_height_on_boundary G.K G.J G.Ω G.y _ G.bd G.snc harith y1 y2 y3
  have hmem : ∀ x, R.lift x x ∈ mcPts (mCoordIdeal G.y) := fun x => R.mem x x (R.mem_U x)
  have horb : ∀ z ∈ mcPts (mCoordIdeal G.y), ∀ z', SameOrbit z' z → z ∈ mcPts G.bd → z' ∈ mcPts G.bd := by
    rintro z hz z' ⟨c, hc, rfl⟩ h
    exact (y2 z ⟨hz, h⟩ c hc).2
  have hBd : ∀ x₀, ∀ x ∈ R.U x₀, R.lift x₀ x ∈ mcPts G.bd ↔ x ∈ bdry s := fun x₀ x hx => by
    rw [hbd]
    exact ⟨horb _ (R.mem _ _ hx) _ (R.compat _ _ _ ⟨R.mem_U _, hx⟩),
      horb _ (hmem x) _ (R.compat _ _ _ ⟨hx, R.mem_U _⟩)⟩
  have hcb1 : ∀ x x', SameOrbit (R.lift x' x') (Cj.cj (R.lift x x)) → x ∈ bdry s → x' ∈ bdry s := fun x x' h hx => by
    rw [hbd] at hx ⊢
    have := y3 _ ⟨hmem x, hx⟩
    exact horb _ this.1 _ h this.2
  have hcb : ∀ x x', SameOrbit (R.lift x' x') (Cj.cj (R.lift x x)) →
      (x' ∈ bdry s ↔ x ∈ bdry s) ∧ rW L s x' = rW L s x := fun x x' h =>
    ⟨⟨hcb1 x' x (by
      have := Cj.sameOrbit_symm (Cj.sameOrbit_cj h)
      rwa [Cj.cj_cj] at this), hcb1 x x' h⟩, hrc x x' h⟩
  have hemb : Cmp.IsEmbedded R.A (mCoordIdeal G.y) R.U R.lift :=
    ⟨R.isOpen_U, R.mem_U, R.holo, R.mem, R.compat, fun z hz => R.surj z hz (not_mem_top _),
      fun x x' h => R.inj x x' (not_mem_top _) h, fun x p hp j hj => R.immersion x (not_mem_top _) p hp j hj⟩
  have hpos : IsPosPot R.A (potOf R (fsHerm G.J (Pi.single G.k₀ 1))) := isPosPot_block R G.k₀ fun x p hp j hj =>
    (GlobalTheory.T.holomorphic_atlas_coord_compat G.𝔐.X G.Ω G.𝔐.ξ G.K G.J G.y G.k₀ G.𝔐.tie G.embeds _ R.X R.A R.U R.lift hemb (G.J G.k₀)
      (Equiv.refl _) x p hp j hj).2
  let d : RootIx D → G.K → ℤ := fun r => -∑ k ∈ Finset.Iic r.2, (sing (r.1, k)).a
  let wt : RootIx D → ((Σ k, G.J k) → ℂ) → ℝ := fun r z =>
    -∑ k ∈ Finset.Iic r.2, Real.log ((sing (r.1, k)).h z) - Real.log ((fsHerm G.J (d r)).h z)
  have hwt : ∀ r z z', (∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0) → SameOrbit z z' → wt r z = wt r z' := fun r z z' hz h =>
    weight_orbit (Finset.Iic r.2) (fun k => sing (r.1, k)) hz h
  let u : RootIx D → R.X → ℝ := fun r x => wt r (R.lift x x)
  have hu : ∀ r x₀, ∀ x ∈ R.U x₀, u r x = wt r (R.lift x₀ x) := fun r x₀ x hx =>
    hwt r _ _ (R.mem _ _ hx).1 (R.compat _ _ _ ⟨R.mem_U _, hx⟩)
  have hball : ∀ᶠ t in 𝓝 (0 : Fin (Top.dimFl (CMType H) (D.p + D.q)) → ℂ), t ∈ ball 0 1 :=
    isOpen_ball.mem_nhds (mem_ball_self one_pos)
  have hsome : ∀ r : RootIx D, ∃ ph phT line C₅ C t₀,
      IsMember R L s (d r) (u r) ((r.2 : ℕ) + 1 = D.p + D.q) ph phT line C₅ C t₀ := by
    intro r
    refine exists_member hI.regGlobal R L s m W hL hs snc hn hcb _ _ _ (fun x x' h => ?_) (fun x => ?_) fun x hx => ?_
    · show wt r _ = wt r _
      rw [hwt r _ _ (Cj.cj_nonzero (hmem x).1) h]
      simp only [wt]
      rw [Cj.fs_conj (d r) (R.lift x x)]
      congr 2
      exact Finset.sum_congr rfl fun k _ => congrArg Real.log (hconj _ _)
    · obtain ⟨ψ, a, M, h⟩ := exists_nchart R.A L s hL hs snc x (R.U x) (R.isOpen_U x) (R.mem_U x)
      refine ⟨ψ, a, M, h, ?_⟩
      have t1 : Tame a _ := (hloc (h.snc R _ (hBd x)) r.1 r.2).1
      have t2 : Tame a fun t => Real.log ((fsHerm G.J (d r)).h (R.lift x (ψ.symm t))) := tame_smooth a fun t ht => by
        obtain ⟨h1, h2, -⟩ := h.2.2.2.2 t ht
        have hz := (R.mem _ _ h2).1
        have hopen : {z : (Σ k, G.J k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} ∈ 𝓝 (R.lift x (ψ.symm t)) := by
          refine Filter.eventually_all.mpr fun k => ?_
          obtain ⟨i, hi⟩ := hz k
          exact Filter.mem_of_superset (((continuous_apply _).isOpen_preimage _ isOpen_ne).mem_nhds hi)
            fun y hy => ⟨i, hy⟩
        have h3 := ((StepW.fsHerm_isSmoothHerm G.K G.J (d r)).contDiffAt hopen).log ((fsHerm G.J (d r)).pos _ hz).ne'
        exact h3.comp t ((analyticAt_lift R h.1 x h1 h2).restrictScalars (𝕜 := ℝ)).contDiffAt
      refine (t1.add (t2.const_mul (-1))).congr ?_
      filter_upwards [hball] with t ht _
      rw [hu r x _ (h.2.2.2.2 t ht).2.1]
      show _ - _ = -∑ k ∈ Finset.Iic r.2, Real.log ((sing (r.1, k)).h (R.lift x (ψ.symm t))) + _
      ring
    · obtain ⟨ψ, a, M, h⟩ := exists_nchart R.A L s hL hs snc x (R.U x) (R.isOpen_U x) (R.mem_U x)
      obtain ⟨p1, p2⟩ := (hloc (h.snc R _ (hBd x)) r.1 r.2).2 (h.zero_of_not_mem hx)
      refine ⟨ψ, h.1, h.2.1, h.2.2.1, p1.congr ?_, fun hc => (p2 hc).congr ?_⟩
      · filter_upwards [hball] with t ht
        rw [hu r x _ (h.2.2.2.2 t ht).2.1]
        show _ + (_ - _) = -∑ k ∈ Finset.Iic r.2, Real.log ((sing (r.1, k)).h (R.lift x (ψ.symm t)))
        ring
      · filter_upwards [hball] with t ht
        rw [hu r x _ (h.2.2.2.2 t ht).2.1]
        show -1 * (_ + (-∑ k ∈ Finset.Iic r.2, Real.log ((sing (r.1, k)).h (R.lift x (ψ.symm t))) - _)) =
          ∑ k ∈ Finset.Iic r.2, Real.log ((sing (r.1, k)).h (R.lift x (ψ.symm t)))
        ring
  choose ph phT line hm using hsome
  obtain ⟨C₅, C, T, hM⟩ := common_members (σ := Option (RootIx D)) (R := R) hL hs snc hn
    (d := fun o => o.elim (Pi.single G.k₀ 1) d) (u := fun o => o.elim 0 u)
    (cen := fun o => o.elim False fun r => (r.2 : ℕ) + 1 = D.p + D.q) (ph := fun o => o.elim 0 ph)
    (phT := fun o => o.elim (fun _ => 0) phT)
    (line := fun o => o.elim (fun _ => fsHerm G.J (Pi.single G.k₀ 1)) line) (by
      rintro (_ | r)
      · exact member_zero R hL hs snc hn _ hpos
      · exact hm r)
  obtain ⟨hA, hfs, hΘ⟩ := fs_pos_potential G.K G.J _ _ R
  let S : AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D)) :=
    { X := R.X
      A := R.A
      Θ := potOf R (fsHerm G.J fun _ => 1)
      L := L
      s := s
      nb := nb
      m := m
      W := W
      potΘ := hA _ hfs
      posΘ := hΘ
      potL := hL
      sec := hs
      snc := snc
      norm_le := hn
      th := fun o => potOf R (fsHerm G.J (o.elim (Pi.single G.k₀ 1) d))
      ph := fun o => o.elim 0 ph
      phT := fun o => o.elim (fun _ => 0) phT
      C₅ := C₅
      C := C
      t₀ := T
      sing := fun o => (hM o).1
      reg := fun o => (hM o).2.1
      c2 := fun o => (hM o).2.2.1 }
  let Re : Realis S (mCoordIdeal G.y) :=
    { arith := harith
      J := ⊤
      R := R
      π := id
      holo := ⟨continuous_id, fun jj k => R.A.holo jj k⟩
      deg := 1
      deg_pos := one_pos
      br := ∅
      degree := FA.degree_id_self R.A
      ref := fun o => fsHerm G.J (o.elim (Pi.single G.k₀ 1) d)
      ref_smooth := fun o => StepW.fsHerm_isSmoothHerm G.K G.J _
      ref_pot := fun o x _ => ⟨Set.univ, isOpen_univ, trivial, fun _ => 0, fun _ => analyticOnNhd_const,
          fun z _ => (sub_self _).trans Complex.zero_re.symm⟩
      line := fun o => o.elim (fun _ => fsHerm G.J (Pi.single G.k₀ 1)) line
      line_deg := fun o t => ((hM o).2.2.2.2.1 t).1
      line_smooth := fun o t _ _ => ((hM o).2.2.2.2.1 t).2.1
      line_eq := fun o t h0 h1 x => (hM o).2.2.2.2.2.1 t h0 h1 x }
  have hnd : (Pi.single G.k₀ 1 : G.K → ℤ) G.k₀ = 1 ∧ ∀ k, k ≠ G.k₀ → (Pi.single G.k₀ 1 : G.K → ℤ) k = 0 :=
    ⟨by simp, fun k hk => by simp [hk]⟩
  refine ⟨{ sing := sing, sing_deg := hdeg, hodge := hhodge, Sys := S, Re := Re, J_top := rfl, deg_one := rfl
            π_bij := Function.bijective_id, embedded := hemb, interior := fun x z hz => ?_
            fund_deg := fun τ i => ?_, fund_sing := fun τ i x hx => ?_
            conj := fun o t => ((hM o).2.2.2.2.1 t).2
            none_deg := hnd
            none_h := fun z => fs_single_h G.k₀ z, pos := hpos, ph_none := fun x => ⟨rfl, fun _ => rfl⟩
            flat := fun τ i hi t => (hM (some (τ, i))).2.2.2.2.2.2 hi t },
    id, ⟨continuous_id, fun jj k => R.A.holo jj k⟩, fun _ => rfl⟩
  · have h1 := G.bd_iff z _ hz
    show _ ↔ ¬ x ∈ bdry s
    rw [hbd]
    tauto
  · show d (τ, i) = _
    simp only [d, hdeg]
  · have h1 : ph (τ, i) x = u (τ, i) x := (hM (some (τ, i))).2.2.2.1 x hx
    show Real.log ((fsHerm G.J (d (τ, i))).h (R.lift x x)) + ph (τ, i) x =
      -∑ k ∈ Finset.Iic i, Real.log ((sing (τ, k)).h (R.lift x x))
    rw [h1]
    simp only [u, wt]
    ring

end AnalyticReference.An
end
end

section -- merged from Development.WeilBound.CoreStatements.CentralCharts.IsCoeffAtOfSmul
noncomputable section

namespace AnalyticReference.An

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open Filter Topology GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

theorem int_frac (F : Type) [Field F] [NumberField F] : Function.Injective (algebraMap (𝓞 F) F) ∧ IsNoetherianRing (𝓞 F) ∧
    ∀ x : F, ∃ a b : 𝓞 F, algebraMap (𝓞 F) F b ≠ 0 ∧ x * algebraMap (𝓞 F) F b = algebraMap (𝓞 F) F a := by
  refine ⟨IsFractionRing.injective _ _, inferInstance, fun x => ?_⟩
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) x
  have : algebraMap (𝓞 F) F b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  exact ⟨a, b, this, div_mul_cancel₀ _ this⟩

theorem isCoeffAt_of_smul {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {V : Type}
    [AddCommGroup V] [Module Ω V] {A B : Lat ξ V} {p q : ℕ} {a a' : ⋀[Ω]^p V} {b b' : ⋀[Ω]^q V} {x : Cpt ξ}
    {d₁ d₂ : Ω} (h₁ : d₁ ≠ 0) (h₂ : d₂ ≠ 0) (ea : a' = d₁ • a) (eb : b' = d₂ • b)
    (h : IsCoeffAt A B p q a' b' x 1) : IsCoeffAt A B p q a b x (d₁ / d₂)⁻¹ := by
  obtain ⟨α, β, hα, hβ, hA, hB, e⟩ := h
  rw [_root_.one_mul] at e
  subst e
  refine ⟨α * d₁, α * d₂, mul_ne_zero hα h₁, mul_ne_zero hα h₂, ?_, ?_, ?_⟩
  · rw [hA, ea, smul_smul]
  · rw [hB, eb, smul_smul]
  · field_simp

theorem unitAt_of_span_eq {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : Cpt ξ}
    {a b : Ω} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : Submodule.span (regAt ξ p) {a} = Submodule.span (regAt ξ p) {b}) : unitAt ξ p (a / b) := by
  obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.1 (h ▸ Submodule.mem_span_singleton_self a :
    a ∈ Submodule.span (regAt ξ p) {b})
  obtain ⟨v, hv⟩ := Submodule.mem_span_singleton.1 (h ▸ Submodule.mem_span_singleton_self b :
    b ∈ Submodule.span (regAt ξ p) {a})
  refine ⟨div_ne_zero ha hb, ?_, ?_⟩
  · have : a / b = (u : Ω) := by rw [← hu]; exact mul_div_cancel_right₀ _ hb
    rw [this]; exact u.2
  · have : (a / b)⁻¹ = (v : Ω) := by rw [inv_div, ← hv]; exact mul_div_cancel_right₀ _ ha
    rw [this]; exact v.2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} [NumberField c.F] {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω : Type}
  [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

theorem exists_cptOver (𝔐 : HodgeCpt Y S y) :
    ∃ (U : Set (Xo.XF c)) (Z : CptOver Y U), genPt 𝔐.ξ₀ = genPt (Z.ξ₀ ≫ Y.j) := by
  have hβ := int_frac c.F
  haveI : IsProper Y.s := GlobalTheory.SchemeWords.isProper_of_isProjOver Y.proj
  haveI : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s
  obtain ⟨W, hW, -, -⟩ := cpt_open_integral Y.X 𝔐.Ω₀ 𝔐.ξ₀ 𝔐.gen₀
  have hsq : (𝔐.ξ ≫ 𝔐.f) ≫ Y.s = spMap 𝔐.cst ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [Category.assoc, 𝔐.cst_over]
    unfold spMap
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let w := pullback.lift (𝔐.ξ ≫ 𝔐.f) (spMap 𝔐.cst) hsq
  have hw1 : w ≫ pullback.fst _ _ = 𝔐.ξ ≫ 𝔐.f := pullback.lift_fst _ _ _
  have hgen : genPt (𝔐.ξ ≫ 𝔐.f) = genPt 𝔐.ξ₀ := by
    rw [show 𝔐.ξ ≫ 𝔐.f = _ from 𝔐.fn_over]
    exact congrArg (fun x => 𝔐.ξ₀ x) (Subsingleton.elim (α := PrimeSpectrum 𝔐.Ω₀) _ _)
  have hne : ((pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F)) ⁻¹ᵁ W : Scheme.Opens _) :
      Set ↥(pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F)))).Nonempty := by
    refine ⟨genPt w, ?_⟩
    have e : genPt (w ≫ pullback.fst _ _) ∈ W := by
      rw [hw1, hgen]
      exact (hW _).2 specializes_rfl
    exact e
  obtain ⟨_, ⟨u, rfl⟩, hu⟩ := Y.jQ_dense.exists_mem_open (TopologicalSpace.Opens.isOpen _) hne
  have hu' : genPt 𝔐.ξ₀ ⤳ Y.j u := (hW _).1 hu
  obtain ⟨Z⟩ := nonempty_cptOver_of_fraction hβ.1 hβ.2.2 Y (irreducibleComponent u)
    (irreducibleComponent_mem_irreducibleComponents u)
  have hz : genPt (Z.ξ₀ ≫ Y.j) ⤳ Y.j u := ((Z.closure u).1 mem_irreducibleComponent).map Y.j.continuous
  exact ⟨_, Z, ((GlobalTheory.CompanionTheory.Ar.genPt_specializes_of_specializes _ 𝔐.gen₀ hu' hz).antisymm
      (GlobalTheory.CompanionTheory.Ar.genPt_specializes_of_specializes _ Z.gen hz hu')).eq⟩

theorem isGeom_of_split (hS : SplitComps Y) {U : Set (Xo.XF c)} (Z : CptOver Y U) : Z.IsGeom := by
  rintro x ⟨f, hf, hx⟩
  letI : Algebra c.F Z.Ω := Z.inc.toAlgebra
  haveI : CharZero Z.Ω := charZero_of_injective_ringHom Z.inc.injective
  haveI : Algebra.IsAlgebraic ℤ c.F := (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ)).2 inferInstance
  have h0 : IsAlgebraic c.F x := ⟨f, hf, hx⟩
  have h1 : IsAlgebraic ℤ x := h0.restrictScalars ℤ
  refine hS Z.Ω (Z.ξ₀ ≫ Y.j) Z.inc Z.gen ?_ x h1
  have e : spMap (Z.inc.comp (algebraMap (𝓞 c.F) c.F)) = spMap Z.inc ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    unfold spMap
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [e, ← Z.over_inc, ← Y.jQ_over]
  simp only [Model.j, Category.assoc, pullback.condition]

theorem central (h0 : FlatLineGenerator) (h1 : FlatLineGeneratorComponent) (hS : SplitComps Y) (hpq : 1 ≤ D.p + D.q) (𝔐 : HodgeCpt Y S y)
    (Fl : 𝔐.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω)
    (hx : CMType H × Fin (D.p + D.q) → HermLine J) (hroot : Fl.RootLines xdeg e)
    (hhod : ∀ r, Fl.IsHodgeLine r (e r) (hx r)) (hdg : ∀ r, (hx r).a = xdeg r) (τ : CMType H) :
    ∃ (c₁ : Ω) (a : K → ℤ) (tt : (c.F →+* ℂ) → ℝ), ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ y z w →
      ∀ cc : (k : K) → J k, (∀ k, w ⟨k, cc k⟩ ≠ 0) →
        (∃ u : ℂ, u ≠ 0 ∧ ValAt 𝔐.ξ z (c₁ / ((∏ k, y ⟨k, cc k⟩ ^ a k) * ∏ i, e (τ, i))) u) ∧
        (𝔐.Interior z → ∀ s : c.F →+* ℂ, (∀ x, ValAt 𝔐.ξ z (𝔐.cst x) (s x)) → ∀ u : ℂ,
          ValAt 𝔐.ξ z (c₁ / ((∏ k, y ⟨k, cc k⟩ ^ a k) * ∏ i, e (τ, i))) u →
          ‖u‖ * ∏ k, ‖w ⟨k, cc k⟩‖ ^ a k = Real.exp (tt s) * ∏ i, (hx (τ, i)).h w) := by
  have hβ := int_frac c.F
  obtain ⟨U, Z, hgp⟩ := exists_cptOver 𝔐
  have hgeom := isGeom_of_split hS Z
  obtain ⟨φ, hφ, hflat, -⟩ := h0 E H D l Xo c _ _ Y U Z τ.1 hβ hpq τ.2 hgeom
  obtain ⟨hinf, -⟩ := h1 E H D l Xo c _ _ Y U Z τ.1 φ hβ hpq τ.2 hgeom hφ hflat
  choose t hinf _ using hinf
  obtain ⟨-, a, b, hgen, hrep⟩ := id hflat
  obtain ⟨i, j, hT⟩ := GlobalTheory.T.hodge_component_matches_model_component E H D l Xo c Y U Z S Ω K J y 𝔐 hgp
  obtain ⟨a', b', d₁, d₂, h₁, h₂, ha0, hb0, ha', hb', ea, eb⟩ :=
    GlobalTheory.T.flag_cm_type_lattice_comparison E H D l Xo c Y U Z S Ω K J y 𝔐 Fl τ i j a b hT hgen
  have hdeg := GlobalTheory.T.hodge_cpt_flag_degree E H D l Xo c _ _ Y S Ω K J y 𝔐 Fl xdeg e τ hroot
  have he : ∏ i, e (τ, i) ≠ 0 := hdeg.1
  have hchar : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective
  have hfr : ∀ p ∈ genFibre ℤ 𝔐.ξ, IsCoeffAt (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) D.p D.q a' b' p 1 := by
    intro p hp
    obtain ⟨⟨x₀, hx₀, ex⟩, hs₁, hs₂⟩ := GlobalTheory.T.cm_type_lattice_comparison E H D l Xo c Y U Z S Ω K J y 𝔐 τ i j hT p hp
    obtain ⟨hv₁, hv₂, -, -⟩ := GlobalTheory.T.eigen_lattice_vector_bundle E H D l Xo c _ _ Y U Z τ.1 hβ τ.2
    obtain ⟨W₁, hW₁, u₁, -, hu₁⟩ := hv₁ x₀ hx₀
    obtain ⟨W₂, hW₂, u₂, -, hu₂⟩ := hv₂ x₀ hx₀
    exact GlobalTheory.T.exterior_coeff_base_change_compat _ _ _ _ _ _ 𝔐.f i _ _ j _ _ _ _ D.p D.q a b a' b' p x₀ u₁ u₂ Z.gen 𝔐.tie.gen hT.1 hT.2.2.1 ex
      (hu₁ x₀ hx₀ hW₁) (hu₂ x₀ hx₀ hW₂) hs₁ hs₂ (hgen.2.2 x₀ hx₀) ha' hb'
  have haF : exteriorPower.ιMulti Ω _ (Fl.b (.inl τ)) ≠ 0 := fun h => ha0 (by
    have e2 : d₁ • (exteriorPower.ιMulti Ω (labelRk D (.inl τ)) (Fl.b (.inl τ))) = 0 := by rw [h, smul_zero]
    exact ea.trans e2)
  have hbF : exteriorPower.ιMulti Ω _ (Fl.b (.inr τ)) ≠ 0 := fun h => hb0 (by
    have e2 : d₂ • (exteriorPower.ιMulti Ω (labelRk D (.inr τ)) (Fl.b (.inr τ))) = 0 := by rw [h, smul_zero]
    exact eb.trans e2)
  have hVA : (𝔐.V (.inl τ)).IsVB (labelRk D (.inl τ)) _ := 𝔐.vb (.inl τ)
  have hVB : (𝔐.V (.inr τ)).IsVB (labelRk D (.inr τ)) _ := 𝔐.vb (.inr τ)
  have hco : ∀ p ∈ genFibre ℤ 𝔐.ξ, IsCoeffAt (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (labelRk D (.inl τ)) (labelRk D (.inr τ))
      (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ))) p (d₁ / d₂)⁻¹ :=
    fun p hp => isCoeffAt_of_smul h₁ h₂ ea eb (hfr p hp)
  have hd0 : d₁ / d₂ ≠ 0 := div_ne_zero h₁ h₂
  let A : HermLine J := PB.combLine (fun i => hx (τ, i)) fun _ => 1
  have hAa : A.a = ∑ i, xdeg (τ, i) := by
    funext k
    simp [A, PB.combLine_a, hdg, Finset.sum_apply]
  have hAh : ∀ w, A.h w = ∏ i, (hx (τ, i)).h w := fun w => by simp [A, PB.combLine_h]
  refine ⟨d₁ / d₂, A.a, t, fun z w hz cc hcc => ⟨?_, fun hint s hs u hu => ?_⟩⟩
  · have hc := 𝔐.all (centre z)
    have hp : (⟨centre z, hc⟩ : Cpt 𝔐.ξ) ∈ genFibre ℤ 𝔐.ξ := fun o ho => by
      have v1 := valAt_int (ξ := 𝔐.ξ) hc o
      have v2 := CxVal.inv v1 (by exact_mod_cast ho)
      obtain ⟨_, s1, e1, -⟩ := v1
      obtain ⟨_, s2, e2, -⟩ := v2
      exact ⟨by simpa using ho, ⟨s1, by simpa using e1⟩, ⟨s2, by simpa using e2⟩⟩
    obtain ⟨-, hL2, -⟩ := GlobalTheory.T.wedge_line_lattice_vector_bundle 𝔐.X Ω 𝔐.ξ 𝔐.Li (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) _ _ _ _ Set.univ
      (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ))) hVA hVB haF hbF
      ⟨_, trivial, _, hco _ hp⟩
    have hgn := (hL2 _ trivial _).2 ⟨hd0, hco _ hp⟩
    have hch := (GlobalTheory.T.frame_domain_in_segre_chart 𝔐.X Ω 𝔐.ξ K J y 𝔐.tie z w cc 1 hc hz
      ⟨hcc, 1, (GlobalTheory.T.valAt_iff_value_at 𝔐.X Ω 𝔐.ξ K J y 𝔐.tie z w hc hz 1 1).1 (CxVal.one hc), one_ne_zero⟩).1
    have h3 := hdeg.2 _ trivial cc hch
    rw [hgn.2, smul_eq_mul, ← hAa] at h3
    refine exists_val_ne hc (unitAt_of_span_eq hd0 (mul_ne_zero ?_ he) h3)
    exact Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hz.2 k (cc k) (IsUnit.mk0 _ (hcc k))).1
  · rw [← hAh]
    refine GlobalTheory.T.flag_weighted_degree_section E H D l Xo c Y S Ω K J y 𝔐 Fl xdeg e hx A τ (t s) (d₁ / d₂) z w hroot hhod hAa
      (fun w'' _ => hAh w'') hz hint hd0 ?_ cc u hcc hu
    intro hc bp bq Γ Δ α κ u' h1 h2 h3 h4 h5 h6 h7 h8 h9
    refine GlobalTheory.T.cm_type_exterior_lattice_comparison E H D l Xo c Y U Z S Ω K J y 𝔐 τ i j a b a' b' φ s _ z hc bp bq Γ Δ (d₁ * α) (d₂ * κ) u' hT hφ
      hgen hrep (hinf _) ha' hb' hint hs h1 h2 h3 h4 h5 h6 ?_ ?_ ?_
    · rw [mul_smul]
      exact ea.trans (congrArg (d₁ • ·) h7)
    · rw [mul_smul]
      exact eb.trans (congrArg (d₂ • ·) h8)
    · rw [← div_mul_div_comm, ← mul_div_assoc]
      exact h9

end AnalyticReference.An
end
end

noncomputable section

namespace AnalyticReference.An

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open Filter Topology

theorem sum_Iic_tele {N : ℕ} (g : ℕ → ℝ) (i : Fin N) :
    ∑ k ∈ Finset.Iic i, (g ((k : ℕ) + 1) - g k) = g ((i : ℕ) + 1) - g 0 := by
  rw [← Finset.sum_range_sub g]
  refine Finset.sum_bij (fun k _ => (k : ℕ)) (fun k hk => ?_) (fun a _ b _ h => Fin.ext h) (fun m hm => ?_)
    fun _ _ => rfl
  · have : k ≤ i := Finset.mem_Iic.1 hk
    exact Finset.mem_range.2 (Nat.lt_succ_of_le this)
  · have h := Finset.mem_range.1 hm
    exact ⟨⟨m, by omega⟩, Finset.mem_Iic.2 (show m ≤ (i : ℕ) by omega), rfl⟩

theorem sum_Ioi_tele {N : ℕ} (g : ℕ → ℝ) (i : Fin N) :
    ∑ k ∈ Finset.Ioi i, (g ((k : ℕ) + 1) - g k) = g N - g ((i : ℕ) + 1) := by
  have h1 : ∑ k : Fin N, (g ((k : ℕ) + 1) - g k) = g N - g 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun k => g (k + 1) - g k) N, Finset.sum_range_sub g]
  have h2 := Finset.sum_add_sum_compl (Finset.Iic i) fun k : Fin N => g ((k : ℕ) + 1) - g k
  rw [sum_Iic_tele, h1, show (Finset.Iic i)ᶜ = Finset.Ioi i by ext; simp] at h2
  linarith

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {Xo : ∀ l : Tor.Level H, Moduli D l} {l : Tor.Level H} {c : Coeff l} [NumberField c.F]
  {Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω : Type} [Field Ω] [CharZero Ω]
  {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

theorem central_chart (h0 : Flat.FlatLineGenerator) (h1 : Flat.FlatLineGeneratorComponent) (hS : SplitComps Y) (hpq : 1 ≤ D.p + D.q)
    (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) {n : ℕ} {Bd : Set ((Σ k, J k) → ℂ)}
    (hBd : ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ y z w → (w ∈ Bd ↔ ¬ 𝔐.Interior z))
    (χ : SncChart (mCoordIdeal y) n Bd) (ha : χ.a = 0) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ)
    (e : CMType H × Fin (D.p + D.q) → Ω) (hx : CMType H × Fin (D.p + D.q) → HermLine J) (hroot : Fl.RootLines xdeg e)
    (hhod : ∀ r, Fl.IsHodgeLine r (e r) (hx r)) (hdg : ∀ r, (hx r).a = xdeg r) (τ : CMType H) :
    ∃ (F : (Fin n → ℂ) → ℂ) (d : ℝ), AnalyticAt ℂ F 0 ∧ F 0 ≠ 0 ∧
      ∀ᶠ t in 𝓝 (0 : Fin n → ℂ), ∑ i, Real.log ((hx (τ, i)).h (χ.γ t)) = Real.log ‖F t‖ + d := by
  have pts : ∀ w ∈ mcPts (mCoordIdeal y), ∃ z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X, CoordsAt 𝔐.ξ y z w := fun w hw => by
    obtain ⟨z, -, hz⟩ := (GlobalTheory.T.complex_points_iff_centres 𝔐.X Ω 𝔐.ξ K J y 𝔐.tie w).1 hw
    exact ⟨z, hz⟩
  obtain ⟨z₀, hz₀⟩ := pts _ (χ.mem 0 (Metric.mem_ball_self one_pos))
  obtain ⟨c₁, a, tt, h⟩ := central h0 h1 hS hpq 𝔐 Fl xdeg e hx hroot hhod hdg τ
  choose cc hcc0 using hz₀.1
  have hc0 : ∀ k, χ.γ 0 ⟨k, cc k⟩ ≠ 0 := fun k => (hcc0 k).ne_zero
  have hcc : ∀ᶠ t in 𝓝 (0 : Fin n → ℂ), ∀ k, χ.γ t ⟨k, cc k⟩ ≠ 0 :=
    eventually_all.2 fun k => (chart_analytic χ _).continuousAt.eventually_ne (hc0 k)
  obtain ⟨⟨v, hv0, hv⟩, -⟩ := h z₀ _ hz₀ cc hc0
  obtain ⟨F₁, hF₁, hF0, hF⟩ := exists_val_fam 𝔐.tie 𝔐.all (chart_analytic χ) hz₀ hv
  obtain ⟨s, hs⟩ := exists_emb_fam 𝔐 (chart_analytic χ) hz₀
  refine ⟨fun t => F₁ t * ∏ k, χ.γ t ⟨k, cc k⟩ ^ a k, -tt s, hF₁.fun_mul
    (Finset.analyticAt_fun_prod _ fun k _ => (chart_analytic χ _).fun_zpow (hc0 k)),
    mul_ne_zero (by rw [hF0]; exact hv0) (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hc0 k)), ?_⟩
  filter_upwards [hF, hcc, hs, Metric.ball_mem_nhds (0 : Fin n → ℂ) one_pos] with t h2 h3 h5 h4
  obtain ⟨z, hz⟩ := pts _ (χ.mem t h4)
  have hi : 𝔐.Interior z := by_contra fun hn => by
    obtain ⟨i, hi, -⟩ := (χ.boundary t h4).1 ((hBd z _ hz).2 hn)
    omega
  have e1 := (h z _ hz cc h3).2 hi s (h5 z hz) _ (h2 z hz)
  have p3 : ∀ i, 0 < (hx (τ, i)).h (χ.γ t) := fun i => (hx _).pos _ fun k => ⟨cc k, h3 k⟩
  simp only [norm_mul, norm_prod, norm_zpow]
  rw [e1, Real.log_mul (Real.exp_ne_zero _) (Finset.prod_ne_zero_iff.2 fun i _ => (p3 i).ne'), Real.log_exp,
    Real.log_prod fun i _ => (p3 i).ne']
  ring

theorem local_bounds (hG : Top.Given) (h0 : Flat.FlatLineGenerator) (h1 : Flat.FlatLineGeneratorComponent) (hGl : Top.IsGlobal Xo l c Y)
    (hS : SplitComps Y) (hpq : 1 ≤ D.p + D.q)
    (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) {n : ℕ} {Bd : Set ((Σ k, J k) → ℂ)}
    (hBd : ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ y z w → (w ∈ Bd ↔ ¬ 𝔐.Interior z))
    (χ : SncChart (mCoordIdeal y) n Bd) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ)
    (e : CMType H × Fin (D.p + D.q) → Ω) (hx : CMType H × Fin (D.p + D.q) → HermLine J) (hroot : Fl.RootLines xdeg e)
    (hhod : ∀ r, Fl.IsHodgeLine r (e r) (hx r)) (hdg : ∀ r, (hx r).a = xdeg r) (τ : CMType H) (i : Fin (D.p + D.q)) :
    Tame χ.a (fun t => -∑ k ∈ Finset.Iic i, Real.log ((hx (τ, k)).h (χ.γ t))) ∧
      (χ.a = 0 → PshAt0 (fun t => -∑ k ∈ Finset.Iic i, Real.log ((hx (τ, k)).h (χ.γ t))) ∧
        ((i : ℕ) + 1 = D.p + D.q → PshAt0 fun t => ∑ k ∈ Finset.Iic i, Real.log ((hx (τ, k)).h (χ.γ t)))) := by
  obtain ⟨M, F, hM0, hM, hF, hev⟩ := root_data hG hGl 𝔐 Fl hBd χ xdeg e hx hroot hhod hdg
  refine ⟨?_, fun ha => ?_⟩
  · have hr : ∀ r, Tame χ.a fun t => Real.log ((hx r).h (χ.γ t)) := fun r => by
      have t1 := (hM _ _ (HodgeCpt.rootIdx D r).2.2).1
      have t2 := (hM _ _ (HodgeCpt.rootIdx D r).2.2.le).1
      refine ((tame_log_norm χ.a (hF r).1 (hF r).2).add ((t1.add (t2.const_mul (-1))).const_mul
        (-((HodgeCpt.rootSgn D r : ℝ) / 2)))).congr ?_
      filter_upwards [hev r] with t ht hoff
      rw [ht hoff]
      simp only [Nat.succ_eq_add_one]
      ring
    refine ((Tame.sum (Finset.Iic i) fun k _ => hr (τ, k)).const_mul (-1)).congr ?_
    exact Eventually.of_forall fun t _ => by ring
  · have hall : ∀ᶠ t in 𝓝 (0 : Fin n → ℂ), ∀ k : Fin (D.p + D.q), _ :=
      eventually_all.2 fun k => (hev (τ, k)).mono fun t ht => ht fun j hj => absurd hj (by omega)
    obtain ⟨Fc, d, hFc, hFc0, hc⟩ := central_chart h0 h1 hS hpq 𝔐 Fl hBd χ ha xdeg e hx hroot hhod hdg τ
    refine ⟨?_, fun hi => ?_⟩
    · by_cases hip : (i : ℕ) < D.p
      · refine ((PshAt0.sum (Finset.Iic i) fun k _ => pshAt0_log_norm (-1) 0 (hF (τ, k)).1 (hF (τ, k)).2).add
          (((hM (.inl τ) ((i : ℕ) + 1) hip).2 ha).const_mul (c := 1 / 2) (by norm_num))).congr ?_
        filter_upwards [hall] with t ht
        have e1 : ∀ k ∈ Finset.Iic i, Real.log ((hx (τ, k)).h (χ.γ t)) = Real.log ‖F (τ, k) t‖ -
            1 / 2 * (M (.inl τ) ((k : ℕ) + 1) t - M (.inl τ) k t) := fun k hk => by
          have hk' : (k : ℕ) < D.p := lt_of_le_of_lt (Fin.le_def.1 (Finset.mem_Iic.1 hk)) hip
          have e2 : HodgeCpt.rootIdx D (τ, k) = ⟨.inl τ, ⟨k, hk'⟩⟩ := dif_pos hk'
          have e3 : HodgeCpt.rootSgn D (τ, k) = 1 := if_pos hk'
          have := ht k
          rw [e2, e3] at this
          simpa using this
        rw [Finset.sum_congr rfl e1, Finset.sum_sub_distrib, ← Finset.mul_sum,
          sum_Iic_tele (fun m => M (.inl τ) m t), hM0]
        simp only [neg_mul, _root_.one_mul, add_zero, Finset.sum_neg_distrib]
        ring
      · refine (((PshAt0.sum (Finset.Ioi i) fun k _ => pshAt0_log_norm 1 0 (hF (τ, k)).1 (hF (τ, k)).2).add
          (((hM (.inr τ) (D.p + D.q - ((i : ℕ) + 1)) (by show _ ≤ D.q; omega)).2 ha).const_mul (c := 1 / 2)
            (by norm_num))).add (pshAt0_log_norm (-1) (-d) hFc hFc0)).congr ?_
        filter_upwards [hall, hc] with t ht hct
        have e1 : ∀ k ∈ Finset.Ioi i, Real.log ((hx (τ, k)).h (χ.γ t)) = Real.log ‖F (τ, k) t‖ -
            1 / 2 * (M (.inr τ) (D.p + D.q - ((k : ℕ) + 1)) t - M (.inr τ) (D.p + D.q - k) t) := fun k hk => by
          have hk0 : (i : ℕ) < k := Fin.lt_def.1 (Finset.mem_Ioi.1 hk)
          have hk' : ¬ (k : ℕ) < D.p := by omega
          have hk2 := k.2
          have e2 : HodgeCpt.rootIdx D (τ, k) = ⟨.inr τ, ⟨D.p + D.q - 1 - k, by show _ < D.q; omega⟩⟩ := dif_neg hk'
          have e3 : HodgeCpt.rootSgn D (τ, k) = -1 := if_neg hk'
          have := ht k
          rw [e2, e3] at this
          have h2 : Real.log ((hx (τ, k)).h (χ.γ t)) = Real.log ‖F (τ, k) t‖ - ((-1 : ℤ) : ℝ) / 2 *
              (M (.inr τ) (D.p + D.q - 1 - k + 1) t - M (.inr τ) (D.p + D.q - 1 - k) t) := this
          rw [show D.p + D.q - 1 - k + 1 = D.p + D.q - k by omega,
            show D.p + D.q - 1 - k = D.p + D.q - (k + 1) by omega] at h2
          rw [h2]
          push_cast
          ring
        have e4 := Finset.sum_add_sum_compl (Finset.Iic i) fun k => Real.log ((hx (τ, k)).h (χ.γ t))
        rw [show (Finset.Iic i)ᶜ = Finset.Ioi i by ext; simp, Finset.sum_congr rfl e1, Finset.sum_sub_distrib,
          ← Finset.mul_sum, sum_Ioi_tele (fun m => M (.inr τ) (D.p + D.q - m) t), Nat.sub_self, hM0, hct] at e4
        simp only [_root_.one_mul, add_zero]
        linarith
    · refine (pshAt0_log_norm 1 d hFc hFc0).congr ?_
      filter_upwards [hc] with t hct
      rw [show Finset.Iic i = Finset.univ by
        ext k
        have := k.2
        simp only [Finset.mem_Iic, Finset.mem_univ, iff_true, Fin.le_def]
        omega, hct, _root_.one_mul]

end AnalyticReference.An

namespace AnalyticReference

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem reference_geometry_holomorphic_inverse : Top.Given → Flat.FlatLineGenerator → Flat.FlatLineGeneratorComponent → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)), Top.IsGlobal Xo l c Y → SplitComps Y → 1 ≤ D.p → 1 ≤ D.q → ∀ G : RefGeo Y, ∃ A : G.An, (∃ inv : A.Sys.X → A.Re.R.X, ReciprocityTheory.AnForm.M.HoloMap A.Sys.A A.Re.R.A inv ∧ ∀ x, inv (A.Re.π x) = x) := by
  intro hG h0 h1 E _ _ _ H D Xo l c Y hGl hS hp hq G
  haveI := c.fin
  haveI : NumberField c.F := {}
  choose sing hdeg hhod hconj using GlobalTheory.T.hodge_cpt_flag_xdeg E H D l (Xo l) c _ _ Y ∅ G.Ω G.K G.J G.y G.𝔐 G.Fl G.xdeg G.e
    RingOfIntegers.coe_injective G.lines
  have hI : PB.Inputs := hG.2.2.2.2.2.2.2.2.2.1
  exact An.of_local hI hp hq G sing hdeg hhod hconj fun χ τ i =>
    An.local_bounds hG h0 h1 hGl hS (by omega) G.𝔐 G.Fl G.bd_iff χ G.xdeg G.e sing G.lines hhod hdeg τ i

end AnalyticReference
