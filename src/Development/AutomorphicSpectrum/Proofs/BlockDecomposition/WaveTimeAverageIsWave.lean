module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandSeriesShiftIdentity
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveSolutionExistence

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveUniqOfWaveSpeed
noncomputable section

open Matrix
open scoped ContDiff
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveK
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveK.Uniq

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Eu_smooth {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (a b : Fin n) :
    ContDiffOn ℝ ∞ (Eu s a b f) (GLs n) := by
  have h := fun X : Mat n => GlobalTheory.CompanionTheory.RCalc.Rd_contDiffOn X hf
  unfold Eu
  exact ((h _).add (contDiffOn_const.smul (h _))).const_smul _

theorem Epow_smooth {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (m : ℕ) :
    ∀ a b : Fin n, ContDiffOn ℝ ∞ (Epow s m a b f) (GLs n) := by
  induction m with
  | zero =>
    intro a b
    by_cases hab : a = b
    · simpa [Epow, hab] using hf
    · simp only [Epow, if_neg hab]
      exact contDiffOn_const (c := (0 : V))
  | succ m ih =>
    intro a b
    have e : Epow s (m + 1) a b f = fun x => ∑ c, Eu s a c (Epow s m c b f) x := by
      ext x
      simp only [Epow, Finset.sum_apply]
    rw [e]
    exact ContDiffOn.sum fun c _ => Eu_smooth (ih c b) s a c

theorem Epow_sub {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (hf' : ContDiffOn ℝ ∞ f' (GLs n))
    (s : Bool) (m : ℕ) :
    ∀ a b : Fin n, Set.EqOn (Epow s m a b (f - f')) (Epow s m a b f - Epow s m a b f') (GLs n) := by
  induction m with
  | zero =>
    intro a b x hx
    by_cases hab : a = b <;> simp [Epow, hab]
  | succ m ih =>
    intro a b x hx
    simp only [Epow, Finset.sum_apply, Pi.sub_apply, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [GlobalTheory.CompanionTheory.WaveAll.Eu_congr GlobalTheory.CompanionTheory.WaveAll.isOpen_GLs (ih c b) s a c hx]
    exact GlobalTheory.CompanionTheory.WaveAll.Eu_sub (Epow_smooth hf s m c b) (Epow_smooth hf' s m c b) s a c hx

theorem gel_sub {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (hf' : ContDiffOn ℝ ∞ f' (GLs n))
    (s : Bool) (m : ℕ) : Set.EqOn (gel s m (f - f')) (gel s m f - gel s m f') (GLs n) := by
  intro x hx
  simp only [gel, Finset.sum_apply, Pi.sub_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun a _ => Epow_sub hf hf' s m a a hx

theorem Om_sub {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (hf' : ContDiffOn ℝ ∞ f' (GLs n)) :
    Set.EqOn (Om (f - f')) (Om f - Om f') (GLs n) := by
  intro x hx
  simp only [Om, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, gel_sub hf hf' _ _ hx, smul_sub, smul_add]
  abel

theorem wave_sub {E : KMod n} {u v : ℝ → Mat n → E.V} (hu : IsWave E u) (hv : IsWave E v) :
    IsWave E (u - v) := by
  refine ⟨?_, fun t => ⟨?_, ?_⟩, fun t g hg => ?_, fun g hg => ?_⟩
  · exact hu.1.sub hv.1
  · exact (hu.2.1 t).1.sub (hv.2.1 t).1
  · intro g hg k
    simp only [Pi.sub_apply, (hu.2.1 t).2 g hg k, (hv.2.1 t).2 g hg k, map_sub]
  · have h1 := (GlobalTheory.CompanionTheory.WaveAll.wave_line hu hg).contDiffAt (x := t)
    have h2 := (GlobalTheory.CompanionTheory.WaveAll.wave_line hv hg).contDiffAt (x := t)
    have e : (fun s => (u - v) s g) = (fun s => u s g) - fun s => v s g := rfl
    rw [e, iteratedDeriv_sub (h1.of_le (WithTop.coe_le_coe.2 le_top)) (h2.of_le (WithTop.coe_le_coe.2 le_top)),
      hu.2.2.1 t g hg, hv.2.2.1 t g hg]
    exact (Om_sub (hu.2.1 t).1 (hv.2.1 t).1 hg).symm
  · have h1 : DifferentiableAt ℝ (fun s => u s g) 0 :=
      ((GlobalTheory.CompanionTheory.WaveAll.wave_line hu hg).differentiable (by simp)).differentiableAt
    have h2 : DifferentiableAt ℝ (fun s => v s g) 0 :=
      ((GlobalTheory.CompanionTheory.WaveAll.wave_line hv hg).differentiable (by simp)).differentiableAt
    have e : (fun s => (u - v) s g) = (fun s => u s g) - fun s => v s g := rfl
    rw [e, deriv_sub h1 h2, hu.2.2.2 g hg, hv.2.2.2 g hg, sub_zero]

theorem waveUniq_of_waveSpeed : WaveSpeed → WaveUniq := by
  intro hS n E u v hu hv h0 t x hx
  obtain ⟨c, hc⟩ := hS n
  have hw := wave_sub hu hv
  have h := hc E (u - v) hw t x hx fun y hy _ => by
    simp only [Pi.sub_apply]
    exact sub_eq_zero.2 (h0 _ (GlobalTheory.CompanionTheory.WaveAll.mul_mem_GLs hx hy))
  exact sub_eq_zero.1 h

end GlobalTheory.CompanionTheory.WaveK.Uniq
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenInvertibleMatrices
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace Convolution
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.AvgJoint

theorem isOpen_invertible_matrices (n : ℕ) : IsOpen (GLs n) := by
  have hc : Continuous (fun y : Mat n => y.det) := Continuous.matrix_det continuous_id
  exact isOpen_ne.preimage hc

theorem avg_joint_smooth : ∀ (n : ℕ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (U : ℝ → Mat n → V) (g : ℝ → ℝ) (T : ℝ), ContDiffOn ℝ ∞ (Function.uncurry U) (Set.univ ×ˢ GLs n) →
    IsBump g T → ContDiffOn ℝ ∞ (Function.uncurry fun t x => ∫ s, (g s : ℂ) • U (t + s) x) (Set.univ ×ˢ GLs n) := by
  intro n V _ _ _ U g T hU hg
  obtain ⟨hgs, hev, hsupp⟩ := hg
  set S : Set (ℝ × Mat n) := Set.univ ×ˢ GLs n with hS
  have hSo : IsOpen S := isOpen_univ.prod (isOpen_invertible_matrices n)
  let h : ℝ × Mat n → ℝ → V := fun p y => ((g (-y) : ℝ) : ℂ) • U (p.1 - y) p.2
  have hh : ContDiffOn ℝ ∞ (Function.uncurry h) (S ×ˢ Set.univ) := by
    have h1 : ContDiff ℝ ∞ (fun q : (ℝ × Mat n) × ℝ => ((g (-q.2) : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (hgs.comp contDiff_snd.neg)
    have h2 : ContDiff ℝ ∞ (fun q : (ℝ × Mat n) × ℝ => (q.1.1 - q.2, q.1.2)) :=
      ((contDiff_fst.comp contDiff_fst).sub contDiff_snd).prodMk (contDiff_snd.comp contDiff_fst)
    have h3 : ContDiffOn ℝ ∞ (fun q : (ℝ × Mat n) × ℝ => Function.uncurry U (q.1.1 - q.2, q.1.2)) (S ×ˢ Set.univ) := by
      refine hU.comp h2.contDiffOn ?_
      rintro ⟨⟨t, x⟩, y⟩ ⟨hp, -⟩
      exact ⟨Set.mem_univ _, hp.2⟩
    exact h1.contDiffOn.smul h3
  have hk : IsCompact (Metric.closedBall (0 : ℝ) |T|) := isCompact_closedBall 0 |T|
  have hz : ∀ p, ∀ x, p ∈ S → x ∉ Metric.closedBall (0 : ℝ) |T| → h p x = 0 := by
    intro p x _ hx
    have hx' : |T| < |x| := by simpa [Metric.mem_closedBall, Real.dist_eq] using hx
    have : g (-x) = 0 := hsupp _ (by rw [abs_neg]; exact lt_of_le_of_lt (le_abs_self T) hx')
    simp [h, this]
  have hloc : LocallyIntegrable (fun _ : ℝ => (1 : ℝ)) (volume : Measure ℝ) :=
    (continuous_const).locallyIntegrable
  have hc := contDiffOn_convolution_right_with_param (𝕜 := ℝ) (μ := (volume : Measure ℝ)) (n := ⊤)
    (f := fun _ : ℝ => (1 : ℝ)) (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] V →L[ℝ] V) hSo hk hz hloc hh
  have hcomp : ContDiffOn ℝ ∞ (fun p : ℝ × Mat n => ((fun _ : ℝ => (1 : ℝ)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h p) 0) S := by
    refine hc.comp (contDiff_id.prodMk contDiff_const).contDiffOn ?_
    intro p hp
    exact ⟨hp, Set.mem_univ _⟩
  refine hcomp.congr ?_
  rintro ⟨t, x⟩ -
  simp [convolution_def, h, Function.uncurry]

end GlobalTheory.CompanionTheory.WaveMult.AvgJoint
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveTimeAverageIsWave
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.WaveAvg

section Generic

variable {P W : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

theorem bump_integrable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {g : ℝ → ℝ} {T : ℝ}
    (hg : Continuous g) (hT : ∀ s, T < |s| → g s = 0) {φ : ℝ → X} (hφ : Continuous φ) :
    Integrable (fun s => g s • φ s) := by
  refine (hg.smul hφ).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) T) ?_
  intro s hs
  have hs' : T < |s| := by simpa [Metric.mem_closedBall, Real.dist_eq] using hs
  simp [hT s hs']

theorem hasFDerivAt_avg {S : Set P} (hS : IsOpen S) {F : P → W} (hF : ContDiffOn ℝ ∞ F S)
    {c : ℝ → P} (hc : Continuous c) (hinv : ∀ p ∈ S, ∀ s, p + c s ∈ S) {g : ℝ → ℝ} {T : ℝ}
    (hg : Continuous g) (hT : ∀ s, T < |s| → g s = 0) {p₀ : P} (hp₀ : p₀ ∈ S) :
    Integrable (fun s => g s • fderiv ℝ F (p₀ + c s)) ∧
      HasFDerivAt (fun p => ∫ s, g s • F (p + c s)) (∫ s, g s • fderiv ℝ F (p₀ + c s)) p₀ := by
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hS.mem_nhds hp₀)
  have hcq : Continuous (fun q : P × ℝ => q.1 + c q.2) :=
    continuous_fst.add (hc.comp continuous_snd)
  have hK : IsCompact ((fun q : P × ℝ => q.1 + c q.2) ''
      (Metric.closedBall p₀ r ×ˢ Set.Icc (-T) T)) :=
    ((isCompact_closedBall p₀ r).prod isCompact_Icc).image hcq
  have hKS : ((fun q : P × ℝ => q.1 + c q.2) ''
      (Metric.closedBall p₀ r ×ˢ Set.Icc (-T) T)) ⊆ S := by
    rintro _ ⟨⟨p, s⟩, ⟨hp, -⟩, rfl⟩
    exact hinv p (hball hp) s
  have hF'c : ContinuousOn (fderiv ℝ F) S := hF.continuousOn_fderiv_of_isOpen hS (by simp)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hF'c.mono hKS)
  have hl : ∀ p ∈ S, Continuous (fun s => F (p + c s)) := fun p hp =>
    hF.continuousOn.comp_continuous (continuous_const.add hc) (hinv p hp)
  have hl' : ∀ p ∈ S, Continuous (fun s => fderiv ℝ F (p + c s)) := fun p hp =>
    hF'c.comp_continuous (continuous_const.add hc) (hinv p hp)
  have hi := bump_integrable hg hT (hl' p₀ hp₀)
  refine ⟨hi, ?_⟩
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
    (F := fun p s => g s • F (p + c s)) (F' := fun p s => g s • fderiv ℝ F (p + c s))
    (bound := fun s => ‖g s‖ * C) (s := Metric.ball p₀ r) (Metric.ball_mem_nhds p₀ hr)
    ?_ ?_ hi.aestronglyMeasurable ?_ ?_ ?_
  · filter_upwards [Metric.ball_mem_nhds p₀ hr] with p hp
    exact (hg.smul (hl p (hball (Metric.ball_subset_closedBall hp)))).aestronglyMeasurable
  · exact bump_integrable hg hT (hl p₀ hp₀)
  · refine .of_forall fun s p hp => ?_
    by_cases hs : T < |s|
    · simp [hT s hs]
    · rw [norm_smul]
      exact mul_le_mul_of_nonneg_left
        (hC _ ⟨(p, s), ⟨Metric.ball_subset_closedBall hp, abs_le.1 (not_lt.1 hs)⟩, rfl⟩)
        (norm_nonneg _)
  · refine (hg.norm.mul continuous_const).integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) T) ?_
    intro s hs
    have hs' : T < |s| := by simpa [Metric.mem_closedBall, Real.dist_eq] using hs
    simp [hT s hs']
  · refine .of_forall fun s p hp => ?_
    have hpS : p + c s ∈ S := hinv p (hball (Metric.ball_subset_closedBall hp)) s
    have hd : HasFDerivAt F (fderiv ℝ F (p + c s)) (p + c s) :=
      ((hF.contDiffAt (hS.mem_nhds hpS)).differentiableAt (by simp)).hasFDerivAt
    exact ((hasFDerivAt_comp_add_right (c s)).2 hd).const_smul (g s)

end Generic

section Ops

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

def av (g : ℝ → ℝ) (U : ℝ → Mat n → V) : ℝ → Mat n → V :=
  fun t x => ∫ s, (g s : ℂ) • U (t + s) x

def JS (U : ℝ → Mat n → V) : Prop :=
  ContDiffOn ℝ ∞ (Function.uncurry U) (Set.univ ×ˢ GLs n)

theorem av_integrable {U : ℝ → Mat n → V} {g : ℝ → ℝ} {T : ℝ} (hU : JS U) (hg : IsBump g T)
    (t : ℝ) {x : Mat n} (hx : x ∈ GLs n) : Integrable (fun s => (g s : ℂ) • U (t + s) x) := by
  have hc : Continuous (fun s => U (t + s) x) :=
    ContinuousOn.comp_continuous (f := fun s : ℝ => (t + s, x)) (g := Function.uncurry U)
      hU.continuousOn ((continuous_const.add continuous_id).prodMk continuous_const)
      (fun s => ⟨Set.mem_univ _, hx⟩)
  simp only [Complex.coe_smul]
  exact bump_integrable hg.1.continuous hg.2.2 hc

variable [CompleteSpace V]

theorem av_smooth {U : ℝ → Mat n → V} {g : ℝ → ℝ} {T : ℝ} (hU : JS U) (hg : IsBump g T) :
    JS (av g U) :=
  GlobalTheory.CompanionTheory.WaveMult.AvgJoint.avg_joint_smooth n U g T hU hg

theorem av_fderiv {U : ℝ → Mat n → V} {g : ℝ → ℝ} {T : ℝ} (hU : JS U) (hg : IsBump g T)
    (t : ℝ) {x : Mat n} (hx : x ∈ GLs n) (w : ℝ × Mat n) :
    fderiv ℝ (Function.uncurry (av g U)) (t, x) w =
      ∫ s, (g s : ℂ) • fderiv ℝ (Function.uncurry U) (t + s, x) w := by
  have hSo : IsOpen ((Set.univ : Set ℝ) ×ˢ GLs n) :=
    isOpen_univ.prod GlobalTheory.CompanionTheory.WaveAll.isOpen_GLs
  have hc : Continuous (fun s : ℝ => ((s, 0) : ℝ × Mat n)) := continuous_id.prodMk continuous_const
  have hinv : ∀ p ∈ (Set.univ : Set ℝ) ×ˢ GLs n, ∀ s : ℝ, p + ((s, 0) : ℝ × Mat n) ∈
      (Set.univ : Set ℝ) ×ˢ GLs n := by
    rintro ⟨a, b⟩ ⟨-, hb⟩ s
    exact ⟨Set.mem_univ _, by simpa using hb⟩
  have h := hasFDerivAt_avg hSo hU hc hinv hg.1.continuous hg.2.2 (p₀ := (t, x))
    ⟨Set.mem_univ _, hx⟩
  have e : Function.uncurry (av g U) =
      fun p : ℝ × Mat n => ∫ s, g s • Function.uncurry U (p + ((s, 0) : ℝ × Mat n)) := by
    funext ⟨a, b⟩
    simp [av, Function.uncurry, Complex.coe_smul]
  have h4 := h.2.fderiv
  rw [← e] at h4
  refine ((DFunLike.congr_fun h4 w).trans (ContinuousLinearMap.integral_apply h.1 w)).trans ?_
  congr 1
  funext s
  simp [Complex.coe_smul]
  rfl

theorem deriv_av {U : ℝ → Mat n → V} {g : ℝ → ℝ} {T : ℝ} (hU : JS U) (hg : IsBump g T)
    (t : ℝ) {x : Mat n} (hx : x ∈ GLs n) :
    deriv (fun r => av g U r x) t = av g (fun s y => deriv (fun r => U r y) s) t x := by
  have hv : JS (av g U) := av_smooth hU hg
  refine (GlobalTheory.CompanionTheory.WaveSpd.SmCalc.deriv_eq GlobalTheory.CompanionTheory.WaveAll.isOpen_GLs hv t hx).trans
    ((av_fderiv hU hg t hx _).trans ?_)
  unfold av
  congr 1
  funext s
  exact congrArg (fun v => (g s : ℂ) • v)
    (GlobalTheory.CompanionTheory.WaveSpd.SmCalc.deriv_eq GlobalTheory.CompanionTheory.WaveAll.isOpen_GLs hU (t + s) hx).symm

theorem Rd_av {U : ℝ → Mat n → V} {g : ℝ → ℝ} {T : ℝ} (hU : JS U) (hg : IsBump g T)
    (X : Mat n) (t : ℝ) {x : Mat n} (hx : x ∈ GLs n) :
    Rd X (av g U t) x = av g (fun s => Rd X (U s)) t x := by
  have hv : JS (av g U) := av_smooth hU hg
  refine (GlobalTheory.CompanionTheory.WaveSpd.SmCalc.fderiv_slice_eq GlobalTheory.CompanionTheory.WaveAll.isOpen_GLs hv t hx (x * X)).trans
    ((av_fderiv hU hg t hx _).trans ?_)
  unfold av
  congr 1
  funext s
  exact congrArg (fun v => (g s : ℂ) • v)
    (GlobalTheory.CompanionTheory.WaveSpd.SmCalc.fderiv_slice_eq GlobalTheory.CompanionTheory.WaveAll.isOpen_GLs hU (t + s) hx (x * X)).symm

def Good (L : (Mat n → V) → (Mat n → V)) : Prop :=
  (∀ U, JS U → JS fun s => L (U s)) ∧
    (∀ f f', Set.EqOn f f' (GLs n) → Set.EqOn (L f) (L f') (GLs n)) ∧
    ∀ (U : ℝ → Mat n → V) (g : ℝ → ℝ) (T : ℝ), JS U → IsBump g T → ∀ t, ∀ x ∈ GLs n,
      L (av g U t) x = av g (fun s => L (U s)) t x

theorem good_id : Good (fun f : Mat n → V => f) :=
  ⟨fun _ h => h, fun _ _ h => h, fun _ _ _ _ _ _ _ _ => rfl⟩

theorem good_zero : Good (fun _ : Mat n → V => (0 : Mat n → V)) := by
  refine ⟨fun U _ => contDiffOn_const (c := (0 : V)), fun _ _ _ _ _ => rfl, ?_⟩
  intro U g T _ _ t x _
  simp [av]

theorem good_Rd (X : Mat n) : Good (Rd (V := V) X) := by
  refine ⟨fun U hU => ?_, fun f f' h => GlobalTheory.CompanionTheory.WaveAll.Rd_congr GlobalTheory.CompanionTheory.WaveAll.isOpen_GLs h X, ?_⟩
  · exact GlobalTheory.CompanionTheory.WaveSpd.SmCalc.smooth_field GlobalTheory.CompanionTheory.WaveAll.isOpen_GLs hU
      (GlobalTheory.CompanionTheory.WaveSpd.SmCalc.contDiff_mulRight X)
  · intro U g T hU hg t x hx
    exact Rd_av hU hg X t hx

theorem good_add {L₁ L₂ : (Mat n → V) → (Mat n → V)} (h₁ : Good L₁) (h₂ : Good L₂) :
    Good (fun f => L₁ f + L₂ f) := by
  refine ⟨fun U hU => (h₁.1 U hU).add (h₂.1 U hU), ?_, ?_⟩
  · intro f f' e x hx
    simp only [Pi.add_apply, h₁.2.1 f f' e hx, h₂.2.1 f f' e hx]
  · intro U g T hU hg t x hx
    simp only [Pi.add_apply]
    rw [h₁.2.2 U g T hU hg t x hx, h₂.2.2 U g T hU hg t x hx]
    unfold av
    rw [← integral_add (av_integrable (h₁.1 U hU) hg t hx) (av_integrable (h₂.1 U hU) hg t hx)]
    congr 1
    funext s
    simp only [Pi.add_apply, smul_add]

theorem good_smul (c : ℂ) {L : (Mat n → V) → (Mat n → V)} (h : Good L) :
    Good (fun f => c • L f) := by
  refine ⟨fun U hU => (h.1 U hU).const_smul c, ?_, ?_⟩
  · intro f f' e x hx
    simp only [Pi.smul_apply, h.2.1 f f' e hx]
  · intro U g T hU hg t x hx
    simp only [Pi.smul_apply]
    rw [h.2.2 U g T hU hg t x hx]
    unfold av
    rw [← integral_smul]
    congr 1
    funext s
    simp only [Pi.smul_apply]
    exact smul_comm c (g s : ℂ) _

theorem good_comp {L₁ L₂ : (Mat n → V) → (Mat n → V)} (h₁ : Good L₁) (h₂ : Good L₂) :
    Good (fun f => L₁ (L₂ f)) := by
  refine ⟨fun U hU => h₁.1 _ (h₂.1 U hU), fun f f' e => h₁.2.1 _ _ (h₂.2.1 f f' e), ?_⟩
  intro U g T hU hg t x hx
  change L₁ (L₂ (av g U t)) x = av g (fun s => L₁ (L₂ (U s))) t x
  rw [h₁.2.1 _ _ (fun y hy => h₂.2.2 U g T hU hg t y hy) hx]
  exact h₁.2.2 _ g T (h₂.1 U hU) hg t x hx

theorem good_sum {ι : Type} (I : Finset ι) {L : ι → (Mat n → V) → (Mat n → V)}
    (h : ∀ i, Good (L i)) : Good (fun f => ∑ i ∈ I, L i f) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using good_zero
  | insert a I ha ih =>
    have e : (fun f => ∑ i ∈ insert a I, L i f) = fun f => L a f + ∑ i ∈ I, L i f := by
      funext f
      rw [Finset.sum_insert ha]
    rw [e]
    exact good_add (h a) ih

theorem good_Eu (s : Bool) (a b : Fin n) : Good (Eu (V := V) s a b) :=
  good_smul _ (good_add (good_Rd _) (good_smul _ (good_Rd _)))

theorem good_Epow (s : Bool) (m : ℕ) : ∀ a b : Fin n, Good (Epow (V := V) s m a b) := by
  induction m with
  | zero =>
    intro a b
    by_cases hab : a = b
    · have e : Epow (V := V) s 0 a b = fun f => f := by
        funext f
        simp [Epow, hab]
      rw [e]
      exact good_id
    · have e : Epow (V := V) s 0 a b = fun _ => 0 := by
        funext f
        simp [Epow, hab]
      rw [e]
      exact good_zero
  | succ m ih =>
    intro a b
    have e : Epow (V := V) s (m + 1) a b = fun f => ∑ c, Eu s a c (Epow s m c b f) := by
      funext f
      simp only [Epow]
    rw [e]
    exact good_sum _ fun c => good_comp (good_Eu s a c) (ih c b)

theorem good_gel (s : Bool) (m : ℕ) : Good (gel (V := V) (n := n) s m) :=
  good_sum _ fun a => good_Epow s m a a

theorem good_Om : Good (Om (V := V) (n := n)) :=
  good_smul _ (good_add (good_gel _ _) (good_gel _ _))

end Ops

theorem iteratedDeriv_two_eq {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : ℝ → V) :
    iteratedDeriv 2 f = deriv (deriv f) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]

theorem isWave_avg : WaveSpeed → ∀ (n : ℕ) (E : KMod n) (u : ℝ → Mat n → E.V) (g : ℝ → ℝ) (T : ℝ),
    IsWave E u → IsBump g T → IsWave E (fun t x => ∫ s, (g s : ℂ) • u (t + s) x) := by
  intro hS n E u g T hu hg
  haveI := FiniteDimensional.complete ℂ E.V
  have hu0 : JS u := hu.1
  have hv : JS (av g u) := av_smooth hu0 hg
  have hu1 : JS (fun s y => deriv (fun r => u r y) s) :=
    GlobalTheory.CompanionTheory.WaveSpd.SmCalc.smooth_deriv GlobalTheory.CompanionTheory.WaveAll.isOpen_GLs hu.1
  change IsWave E (av g u)
  refine ⟨hv, fun t => ⟨GlobalTheory.CompanionTheory.WaveSpd.SmCalc.smooth_slice hv t, ?_⟩, ?_, ?_⟩
  · intro x hx k
    have hint := av_integrable hu0 hg t hx
    change ∫ s, (g s : ℂ) • u (t + s) (x * k.1) = E.ρ k⁻¹ (∫ s, (g s : ℂ) • u (t + s) x)
    rw [← (E.ρ k⁻¹).integral_comp_comm hint]
    congr 1
    funext s
    rw [(hu.2.1 (t + s)).2 x hx k, map_smul]
  · intro t x hx
    have e1 : deriv (fun r => av g u r x) =
        fun t => av g (fun s y => deriv (fun r => u r y) s) t x :=
      funext fun t => deriv_av hu0 hg t hx
    rw [iteratedDeriv_two_eq, e1, deriv_av hu1 hg t hx, good_Om.2.2 u g T hu0 hg t x hx]
    unfold av
    congr 1
    funext s
    have h := hu.2.2.1 (t + s) x hx
    rw [iteratedDeriv_two_eq] at h
    exact congrArg (fun v => (g s : ℂ) • v) h
  · intro x hx
    rw [deriv_av hu0 hg 0 hx]
    have hU := GlobalTheory.CompanionTheory.WaveK.Uniq.waveUniq_of_waveSpeed hS n E (fun s => u (-s)) u
      (GlobalTheory.CompanionTheory.WaveSpd.isWave_time_refl E u hu) hu (fun y _ => by simp)
    have ev : (fun r => u (-r) x) = fun r => u r x := funext fun r => hU r x hx
    have odd : ∀ s, deriv (fun r => u r x) (-s) = -deriv (fun r => u r x) s := by
      intro s
      have h := deriv_comp_neg (𝕜 := ℝ) (fun r => u r x) s
      rw [ev] at h
      rw [h, neg_neg]
    have h1 : ∫ s, ((g (-s) : ℝ) : ℂ) • deriv (fun r => u r x) (-s) =
        ∫ s, (g s : ℂ) • deriv (fun r => u r x) s :=
      integral_neg_eq_self (fun s => (g s : ℂ) • deriv (fun r => u r x) s) volume
    have h2 : (fun s => ((g (-s) : ℝ) : ℂ) • deriv (fun r => u r x) (-s)) =
        fun s => -((g s : ℂ) • deriv (fun r => u r x) s) := by
      funext s
      rw [hg.2.1 s, odd s, smul_neg]
    rw [h2, integral_neg] at h1
    have h3 : ∫ s, (g s : ℂ) • deriv (fun r => u r x) s = 0 := by
      generalize (∫ s, (g s : ℂ) • deriv (fun r => u r x) s) = I at h1 ⊢
      have h5 : (2 : ℝ) • I = 0 := by
        rw [two_smul]
        nth_rw 1 [← h1]
        exact neg_add_cancel I
      exact (smul_eq_zero.1 h5).resolve_left two_ne_zero
    simpa [av] using h3

end GlobalTheory.CompanionTheory.WaveMult.WaveAvg
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveTimeAverageIsWaveStatement
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wave_time_average_is_wave : WaveSpeed → ∀ (n : ℕ) (E : KMod n) (u : ℝ → Mat n → E.V) (g : ℝ → ℝ) (T : ℝ), IsWave E u → IsBump g T → IsWave E (fun t x => ∫ s, (g s : ℂ) • u (t + s) x) := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.WaveAvg.isWave_avg | exact GlobalTheory.CompanionTheory.WaveMult.WaveAvg.isWave_avg | (intros; apply GlobalTheory.CompanionTheory.WaveMult.WaveAvg.isWave_avg <;> assumption)
end
