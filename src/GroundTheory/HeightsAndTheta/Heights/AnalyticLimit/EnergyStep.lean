module

public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StTailLogOfMass

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.EnergyStep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.M

noncomputable section

structure EnergyStep.Data {n : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas (n + 1) X)
    (Om : KaehlerForm A) where

  w : X → ℝ

  v : X → ℝ

  f : Fin n → X → ℝ

  M : ℝ
  w_smooth : A.Smooth w
  w_psh : IsPsh A (Om.pot + LocPot.ofFun w)
  v_smooth : A.Smooth v
  v_nonpos : ∀ x, v x ≤ 0
  le_v : ∀ x, -M ≤ v x
  f_smooth : ∀ i, A.Smooth (f i)
  f_psh : ∀ i, IsPsh A (Om.pot + LocPot.ofFun (f i))

def EnergyStep.Data.T {n : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas (n + 1) X}
    {Om : KaehlerForm A} (d : EnergyStep.Data A Om) : Fin n → LocPot X :=
  fun i => Om.pot + LocPot.ofFun (d.f i)

def EnergyStep.Statement : Prop :=
  ∀ {n : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas (n + 1) X) (Om : KaehlerForm A) (d : EnergyStep.Data A Om),
    mInt A (Fin.cons (Om.pot + LocPot.ofFun d.v) d.T) (fun x => -d.w x) ≤
      mInt A (Fin.cons Om.pot d.T) (fun x => -d.w x) + d.M * Om.vol

theorem KaehlerForm.isPsh {n : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas n X}
    (Om : KaehlerForm A) : IsPsh A Om.pot := by
  intro x j y hy z
  by_cases hz : z = 0
  · subst hz
    simp [levi]
  · exact (Om.pos x j y hy z hz).le

theorem levi_add_const {ι : Type} [Fintype ι] (g : (ι → ℂ) → ℝ) (c : ℝ) (y z : ι → ℂ) :
    levi (fun y' => g y' + c) y z = levi g y z := by
  have h : fderiv ℝ (fun y' => g y' + c) = fderiv ℝ g := funext fun y' => fderiv_add_const c
  unfold levi
  rw [h]

theorem isPsh_add_const {n : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas n X}
    {P : LocPot X} (hP : IsPsh A P) (c : ℝ) : IsPsh A (P + LocPot.ofFun fun _ => c) := by
  intro x j y hy z
  have h : (P + LocPot.ofFun fun _ => c).φ x ∘ (A.chart j).symm =
      fun y' => (P.φ x ∘ (A.chart j).symm) y' + c := rfl
  rw [h, levi_add_const]
  exact hP x j y ⟨hy.1, hy.2.1⟩ z

theorem mInt_neg {n : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas n X) (Φ : Fin n → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (g : X → ℝ)
    (hg : MIntegrable A Φ g) : mInt A Φ (fun x => -g x) = -mInt A Φ g := by
  have h := mIntLinear A Φ hΦ (-1) g (fun _ => 0) hg (mIntegrableCont A Φ hΦ _ continuous_const)
  simp only [neg_one_mul, add_zero, st_mInt_zero] at h
  exact h

theorem EnergyStep.proof : EnergyStep.Statement := by
  intro n X _ _ _ A Om d
  have hT : ∀ i, IsPotential A (d.T i) := fun i =>
    isPotentialAdd A _ _ Om.isPot (isPotential_ofFun A _ (d.f_smooth i))
  have hcons : ∀ P, IsPotential A P → ∀ i, IsPotential A ((Fin.cons P d.T : Fin (n + 1) → LocPot X) i) := by
    intro P hP i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using hP
    · simpa using hT i
  have hw := isPotential_ofFun A _ d.w_smooth
  have hv := isPotential_ofFun A _ d.v_smooth
  have hOw := isPotentialAdd A _ _ Om.isPot hw
  have cw := st_smooth_continuous A d.w_smooth
  have cv := st_smooth_continuous A d.v_smooth
  have int : ∀ P, IsPotential A P → ∀ g : X → ℝ, Continuous g →
      MIntegrable A (Fin.cons P d.T) g := fun P hP g hg => mIntegrableCont A _ (hcons P hP) g hg

  have h1 := mIntAdd A Om.pot (LocPot.ofFun d.v) d.T Om.isPot hv hT (fun x => -d.w x)
    (int _ Om.isPot _ cw.neg) (int _ hv _ cw.neg)
  have h2 := mInt_neg A _ (hcons _ hv) d.w (int _ hv _ cw)
  have h3 := (byPartsSymm A d.v d.w d.v_smooth d.w_smooth d.T hT).symm
  have h4 := mIntAdd A Om.pot (LocPot.ofFun d.w) d.T Om.isPot hw hT d.v
    (int _ Om.isPot _ cv) (int _ hw _ cv)
  have hpsh : ∀ P, IsPsh A P → ∀ i, IsPsh A ((Fin.cons P d.T : Fin (n + 1) → LocPot X) i) := by
    intro P hP i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using hP
    · exact d.f_psh i

  have h5 := mIntNonneg A _ (hcons _ Om.isPot) (hpsh _ Om.isPsh) (fun x => -d.v x)
    fun x => by have := d.v_nonpos x; linarith
  rw [mInt_neg A _ (hcons _ Om.isPot) d.v (int _ Om.isPot _ cv)] at h5

  have h6 := mIntLinear A _ (hcons _ hOw) d.M (fun _ => 1) d.v (int _ hOw _ continuous_const)
    (int _ hOw _ cv)
  beta_reduce at h6
  have h7 := mIntNonneg A _ (hcons _ hOw) (hpsh _ d.w_psh) (fun x => d.M * 1 + d.v x)
    fun x => by have := d.le_v x; linarith
  rw [h6] at h7

  have h8 := mIntAdd A Om.pot (LocPot.ofFun d.w) d.T Om.isPot hw hT (fun _ => 1)
    (int _ Om.isPot _ continuous_const) (int _ hw _ continuous_const)
  have h9 := stokes A d.w d.w_smooth d.T hT
  have h10 := massIndep A (fun _ => Om.pot) (Fin.cons (fun _ => 0) d.f) (fun _ => Om.isPot)
    (by
      intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa using st_smooth_const A 0
      · simpa using d.f_smooth i)
  have h11 : mInt A (Fin.cons Om.pot d.T) (fun _ => 1) =
      mInt A (fun i => Om.pot + LocPot.ofFun ((Fin.cons (fun _ => 0) d.f : Fin (n + 1) → X → ℝ) i))
        (fun _ => 1) := by
    apply st_mInt_congr_phi
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · funext x y
      show Om.pot.φ x y = Om.pot.φ x y + 0
      ring
    · rfl
  have hV : mInt A (Fin.cons Om.pot d.T) (fun _ => 1) = Om.vol := by
    rw [h11, h10]
    rfl
  rw [h8, h9, add_zero, hV] at h7
  rw [h1, h2, h3]
  linarith [h4, h5, h7]

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PGreenMassZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory Filter Topology
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPsh IsPosPot IsSection logNormSec mInt
  MIntegrable maMeasure maMeasure_thm logNormIntegrable mIntegrableCont)

noncomputable section

theorem continuousAt_of_charts {e : ℕ} {X : Type} [TopologicalSpace X] {E : Type}
    [TopologicalSpace E] (A : FinHolAtlas e X) {U : Set X} (hU : IsOpen U) (g : X → E)
    (hg : ∀ j, ContinuousOn (g ∘ (A.chart j).symm) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U))
    {y : X} (hy : y ∈ U) : ContinuousAt g y := by
  obtain ⟨j, hj⟩ := A.cover y
  set c := A.chart j
  have hopen : IsOpen (c.target ∩ c.symm ⁻¹' U) := c.isOpen_inter_preimage_symm hU
  have hmem : c y ∈ c.target ∩ c.symm ⁻¹' U := ⟨c.map_source hj, by
    show c.symm (c y) ∈ U
    rw [c.left_inv hj]
    exact hy⟩
  have h1 : ContinuousAt (g ∘ c.symm) (c y) := (hg j).continuousAt (hopen.mem_nhds hmem)
  have h2 : ContinuousAt ((g ∘ c.symm) ∘ c) y := h1.comp (c.continuousAt hj)
  refine h2.congr ?_
  filter_upwards [c.open_source.mem_nhds hj] with z hz
  simp [Function.comp, c.left_inv hz]

theorem continuous_secNorm {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (L : LocPot X) (s : X → X → ℂ) (hL : IsPotential A L) (hs : IsSection A L s) :
    Continuous (secNorm L s) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  have hsc : ContinuousAt (s x₀) x₀ := continuousAt_of_charts A (L.isOpen_U x₀) (s x₀)
    (fun j => (hs.1 x₀ j).continuousOn) (L.mem_U x₀)
  have hφc : ContinuousAt (L.φ x₀) x₀ := continuousAt_of_charts A (L.isOpen_U x₀) (L.φ x₀)
    (fun j => (hL.1 x₀ j).continuousOn) (L.mem_U x₀)
  have hf : ContinuousAt (fun y => ‖s x₀ y‖ * Real.exp (-L.φ x₀ y)) x₀ :=
    hsc.norm.mul (Real.continuous_exp.continuousAt.comp hφc.neg)
  refine hf.congr ?_
  filter_upwards [(L.isOpen_U x₀).mem_nhds (L.mem_U x₀)] with y hy
  exact hs.2 x₀ y y ⟨hy, L.mem_U y⟩

theorem isPsh_of_isPosPot {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (P : LocPot X) (hP : IsPosPot A P) : IsPsh A P := by
  intro x j y hy w
  by_cases hw : w = 0
  · subst hw
    simp [levi]
  · exact (hP x j y hy w hw).le

theorem greenEp_nonneg {W : Type} [TopologicalSpace W] (L : LocPot W) (s : W → W → ℂ) {ε : ℝ}
    (hε : 0 ≤ ε) (x : W) : 0 ≤ greenEp L s ε x := by
  unfold greenEp
  apply Real.log_nonneg
  have : 0 ≤ ε / secNorm L s x ^ 2 := div_nonneg hε (sq_nonneg _)
  linarith

theorem greenEp_le_one {W : Type} [TopologicalSpace W] (L : LocPot W) (s : W → W → ℂ) {ε : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (x : W) : greenEp L s ε x ≤ greenEp L s 1 x := by
  unfold greenEp
  have h0 : 0 ≤ ε / secNorm L s x ^ 2 := div_nonneg hε (sq_nonneg _)
  apply Real.log_le_log (by linarith)
  have : ε / secNorm L s x ^ 2 ≤ 1 / secNorm L s x ^ 2 :=
    div_le_div_of_nonneg_right hε1 (sq_nonneg _)
  linarith

theorem greenEp_one_eq {W : Type} [TopologicalSpace W] (L : LocPot W) (s : W → W → ℂ) (x : W) :
    greenEp L s 1 x = Real.log (secNorm L s x ^ 2 + 1) - 2 * logNormSec L s x := by
  have hl : logNormSec L s x = Real.log (secNorm L s x) := rfl
  unfold greenEp
  rw [hl]
  by_cases hN : secNorm L s x = 0
  · simp [hN]
  · have h2 : secNorm L s x ^ 2 ≠ 0 := pow_ne_zero 2 hN
    have h3 : secNorm L s x ^ 2 + 1 ≠ 0 := by positivity
    rw [show 1 + 1 / secNorm L s x ^ 2 = (secNorm L s x ^ 2 + 1) / secNorm L s x ^ 2 by
      field_simp, Real.log_div h3 h2, Real.log_pow]
    push_cast
    ring

theorem greenEp_tendsto_zero {W : Type} [TopologicalSpace W] (L : LocPot W) (s : W → W → ℂ)
    (x : W) : Tendsto (fun ε => greenEp L s ε x) (𝓝[>] 0) (𝓝 0) := by
  unfold greenEp
  set c := secNorm L s x ^ 2
  have hc : ContinuousAt (fun ε : ℝ => 1 + ε / c) 0 :=
    (continuous_const.add (continuous_id.div_const c)).continuousAt
  have hlog : ContinuousAt (fun ε : ℝ => Real.log (1 + ε / c)) 0 := hc.log (by simp)
  have ht := hlog.tendsto
  simp only [zero_div, add_zero, Real.log_one] at ht
  exact tendsto_nhdsWithin_of_tendsto_nhds ht

theorem GreenMassZero.proof : GreenMassZero.Statement := by
  intro D W _ _ _ S η hη
  let : MeasurableSpace W := borel W
  have : BorelSpace W := ⟨rfl⟩
  set Φ : Fin (D + 1) → LocPot W := fun _ => S.Om.pot with hΦdef
  have hΦ : ∀ i, IsPotential S.A (Φ i) := fun _ => S.Om.isPot
  have hΦpsh : ∀ i, IsPsh S.A (Φ i) := fun _ => isPsh_of_isPosPot S.A _ S.Om.pos
  obtain ⟨hfin, hμ⟩ := maMeasure_thm S.A Φ hΦ hΦpsh
  set μ := maMeasure S.A Φ
  have hN : Continuous (secNorm S.L S.s) := continuous_secNorm S.A S.L S.s S.L_pot S.s_sec
  have hmeas : ∀ ε, Measurable (greenEp S.L S.s ε) := fun ε =>
    ((hN.measurable.pow_const 2).const_div ε |>.const_add 1).log

  have hlogN : Integrable (logNormSec S.L S.s) μ := by
    have hm : Measurable (logNormSec S.L S.s) := hN.measurable.log
    exact ((hμ _ hm).1).1 (logNormIntegrable S.A S.L S.s S.mult S.comp S.L_pot S.s_sec S.s_snc Φ hΦ)
  have hh : Integrable (fun x => Real.log (secNorm S.L S.s x ^ 2 + 1)) μ := by
    have hc : Continuous fun x => Real.log (secNorm S.L S.s x ^ 2 + 1) :=
      ((hN.pow 2).add continuous_const).log fun x =>
        (by positivity : (0 : ℝ) < secNorm S.L S.s x ^ 2 + 1).ne'
    exact ((hμ _ hc.measurable).1).1 (mIntegrableCont S.A Φ hΦ _ hc)
  have hG1 : Integrable (greenEp S.L S.s 1) μ := by
    have : greenEp S.L S.s 1 = fun x =>
        Real.log (secNorm S.L S.s x ^ 2 + 1) - 2 * logNormSec S.L S.s x :=
      funext (greenEp_one_eq S.L S.s)
    rw [this]
    exact hh.sub (hlogN.const_mul 2)
  have hnorm : ∀ ε, 0 < ε → ε ≤ 1 → ∀ x, ‖greenEp S.L S.s ε x‖ ≤ greenEp S.L S.s 1 x :=
    fun ε hε hε1 x => by
      rw [Real.norm_of_nonneg (greenEp_nonneg S.L S.s hε.le x)]
      exact greenEp_le_one S.L S.s hε.le hε1 x

  have hJ : ∀ ε, 0 < ε → ε ≤ 1 → ∀ t, S.J 0 ε t = ∫ x, greenEp S.L S.s ε x ∂μ := by
    intro ε hε hε1 t
    have hmix : mixedForms S.Om.pot (S.T t) 0 = Φ := by
      funext i
      simp [mixedForms, hΦdef]
    have hint : Integrable (greenEp S.L S.s ε) μ :=
      hG1.mono' (hmeas ε).aestronglyMeasurable (ae_of_all _ (hnorm ε hε hε1))
    have hmi : MIntegrable S.A Φ (greenEp S.L S.s ε) := ((hμ _ (hmeas ε)).1).2 hint
    show mInt S.A (mixedForms S.Om.pot (S.T t) 0) (greenEp S.L S.s ε) = _
    rw [hmix]
    exact (hμ _ (hmeas ε)).2 hmi

  have hT : Tendsto (fun ε => ∫ x, greenEp S.L S.s ε x ∂μ) (𝓝[>] 0) (𝓝 0) := by
    have := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := 𝓝[>] (0 : ℝ))
      (F := fun ε x => greenEp S.L S.s ε x) (f := fun _ => (0 : ℝ)) (greenEp S.L S.s 1)
      (Eventually.of_forall fun ε => (hmeas ε).aestronglyMeasurable)
      (eventually_of_mem (Ioc_mem_nhdsGT zero_lt_one) fun ε hε => ae_of_all _ (hnorm ε hε.1 hε.2))
      hG1 (ae_of_all _ fun x => greenEp_tendsto_zero S.L S.s x)
    simpa using this
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∫ x, greenEp S.L S.s ε x ∂μ < η := (tendsto_order.1 hT).2 η hη
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  have hu0 : (0 : ℝ) < u := hu
  refine ⟨min (u / 2) 1, lt_min (by linarith) one_pos, fun ε hε hεle t => ?_⟩
  have hε1 : ε ≤ 1 := hεle.trans (min_le_right _ _)
  have hεu : ε < u := lt_of_le_of_lt (hεle.trans (min_le_left _ _)) (by linarith)
  rw [hJ ε hε hε1 t]
  exact (hsub ⟨hε, hεu⟩).le

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.SystemIndependence
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory Filter Topology
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential mInt MIntegrable)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData ell errE)

noncomputable section

namespace SystemIndependence

section Integrals

variable {D : ℕ} {X : Type} [TopologicalSpace X]

theorem mIntegrable_linComb (A : FinHolAtlas D X) (Φ : Fin D → LocPot X) (c : ℝ) {f f' : X → ℝ}
    (hf : MIntegrable A Φ f) (hf' : MIntegrable A Φ f') :
    MIntegrable A Φ (fun x => c * f x + f' x) := fun j K hK hKc =>
  IntegrableOn.congr_fun (((hf j K hK hKc).const_mul c).add (hf' j K hK hKc))
    (fun y _ => by simp only [Pi.add_apply]; ring) hKc.measurableSet

theorem mIntegrable_zero (A : FinHolAtlas D X) (Φ : Fin D → LocPot X) :
    MIntegrable A Φ (fun _ => 0) := fun j K _ _ => by
  simp

theorem mInt_zero (A : FinHolAtlas D X) (Φ : Fin D → LocPot X) : mInt A Φ (fun _ => 0) = 0 := by
  unfold mInt ReciprocityTheory.AnForm.M.integralWith
  split_ifs <;> simp

theorem mInt_nonneg_on (A : FinHolAtlas D X) (V : Set X) (Φ : Fin D → LocPot X)
    (hpot : ∀ i, IsPotential A (Φ i)) (hnn : ∀ i, FormNonneg A V (Φ i)) (f : X → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hf0 : ∀ x ∉ V, f x = 0) : 0 ≤ mInt A Φ f := by
  unfold mInt
  split_ifs with h
  · unfold ReciprocityTheory.AnForm.M.integralWith
    refine Finset.sum_nonneg fun j _ =>
      setIntegral_nonneg (A.chart j).open_target.measurableSet fun y hy => ?_
    by_cases hyV : (A.chart j).symm y ∈ V
    · have hd : 0 ≤ ReciprocityTheory.AnForm.M.locDens A Φ j y :=
        ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ y fun i =>
          ReciprocityTheory.AnForm.M.hessC_posSemidef_of_levi _ y
            (ReciprocityTheory.AnForm.M.pot_contDiffAt_two (hpot i) _ j hy ((Φ i).mem_U _))
            (fun w => hnn i _ j y ⟨hy, hyV, (Φ i).mem_U _⟩ w)
      exact mul_nonneg (mul_nonneg (h.some.nonneg j _) (hf _)) hd
    · rw [hf0 _ hyV]
      simp
  · exact le_rfl

theorem abs_mInt_le [CompactSpace X] [T2Space X] (A : FinHolAtlas D X) (V : Set X)
    (Φ : Fin D → LocPot X) (hpot : ∀ i, IsPotential A (Φ i)) (hnn : ∀ i, FormNonneg A V (Φ i))
    (hAn : A.IsAnalyticSubset Vᶜ) (hint : interior Vᶜ = ∅) {h b : X → ℝ}
    (hh : MIntegrable A Φ h) (hb : MIntegrable A Φ b) (hle : ∀ x ∈ V, |h x| ≤ b x) :
    |mInt A Φ h| ≤ mInt A Φ b := by
  have key : ∀ c : ℝ, |c| = 1 → 0 ≤ mInt A Φ (fun x => c * h x + b x) := by
    intro c hc
    have hcongr := ReciprocityTheory.AnForm.M.mIntCongrNull A Φ Vᶜ hAn hint (fun x => c * h x + b x)
      (V.indicator fun x => c * h x + b x) (fun x hx => by
        rw [Set.indicator_of_mem (Set.not_notMem.mp hx)])
    rw [hcongr]
    refine mInt_nonneg_on A V Φ hpot hnn _ (fun x => ?_) (fun x hx => Set.indicator_of_notMem hx _)
    by_cases hx : x ∈ V
    · rw [Set.indicator_of_mem hx]
      have h1 := hle x hx
      have h2 : |c * h x| = |h x| := by rw [abs_mul, hc, one_mul]
      have h3 := neg_abs_le (c * h x)
      linarith
    · rw [Set.indicator_of_notMem hx]
  have l1 := ReciprocityTheory.AnForm.M.mIntLinear A Φ hpot (-1) h b hh hb
  have l2 := ReciprocityTheory.AnForm.M.mIntLinear A Φ hpot 1 h b hh hb
  have k1 := key (-1) (by norm_num)
  have k2 := key 1 (by norm_num)
  rw [abs_le]
  constructor <;> linarith

end Integrals

end SystemIndependence

section Inhabitant

open ReciprocityTheory.AnForm.M (p1)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData)

end Inhabitant

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLemmaETailLog
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection logNormSec)

variable {D : ℕ} {X : Type*} [TopologicalSpace X]

theorem continuousAt_of_chart {β : Type*} [TopologicalSpace β] (A : FinHolAtlas D X) {f : X → β}
    {U : Set X} (hU : IsOpen U) {z : X} (hz : z ∈ U) (j : Fin A.n) (hzj : z ∈ (A.chart j).source)
    (hf : ContinuousOn (f ∘ (A.chart j).symm) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U)) :
    ContinuousAt f z := by
  set c := A.chart j
  have hmem : c z ∈ c.target ∩ c.symm ⁻¹' U := ⟨c.map_source hzj, by simpa [c.left_inv hzj] using hz⟩
  have h1 : ContinuousAt (f ∘ c.symm) (c z) :=
    hf.continuousAt ((c.isOpen_inter_preimage_symm hU).mem_nhds hmem)
  have h2 : ContinuousAt (f ∘ c.symm ∘ c) z := h1.comp (c.continuousAt hzj)
  refine h2.congr ?_
  filter_upwards [c.open_source.mem_nhds hzj] with y hy
  simp [c.left_inv hy]

theorem normSec_eventuallyEq {A : FinHolAtlas D X} {L : LocPot X} {s : X → X → ℂ}
    (hs : IsSection A L s) (y : X) :
    (fun z => ‖s z z‖ * Real.exp (-L.φ z z)) =ᶠ[𝓝 y] fun z => ‖s y z‖ * Real.exp (-L.φ y z) := by
  filter_upwards [(L.isOpen_U y).mem_nhds (L.mem_U y)] with z hz
  exact hs.2 z y z ⟨L.mem_U z, hz⟩

theorem continuous_normSec {A : FinHolAtlas D X} {L : LocPot X} {s : X → X → ℂ}
    (hL : IsPotential A L) (hs : IsSection A L s) :
    Continuous fun z => ‖s z z‖ * Real.exp (-L.φ z z) := by
  refine continuous_iff_continuousAt.2 fun y => ?_
  obtain ⟨j, hj⟩ := A.cover y
  have h : ContinuousAt (fun z => ‖s y z‖ * Real.exp (-L.φ y z)) y := by
    refine continuousAt_of_chart A (L.isOpen_U y) (L.mem_U y) j hj ?_
    have h1 := (hs.1 y j).continuousOn
    have h2 := (hL.1 y j).continuousOn
    exact h1.norm.mul (Real.continuous_exp.comp_continuousOn h2.neg)
  exact h.congr (normSec_eventuallyEq hs y).symm

theorem isOpen_secOpen {A : FinHolAtlas D X} {L : LocPot X} {s : X → X → ℂ}
    (hL : IsPotential A L) (hs : IsSection A L s) : IsOpen (secOpen s) := by
  have h : secOpen s = (fun z => ‖s z z‖ * Real.exp (-L.φ z z)) ⁻¹' {0}ᶜ := by
    ext y
    simp [secOpen, Real.exp_ne_zero]
  rw [h]
  exact (continuous_normSec hL hs).isOpen_preimage _ isOpen_compl_singleton

theorem continuousOn_rSec {A : FinHolAtlas D X} {L : LocPot X} {s : X → X → ℂ}
    (hL : IsPotential A L) (hs : IsSection A L s) : ContinuousOn (rSec L s) (secOpen s) := by
  refine continuousOn_const.sub (continuousOn_const.mul
    ((continuous_normSec hL hs).continuousOn.log fun y hy => ?_))
  exact mul_ne_zero (norm_ne_zero_iff.2 hy) (Real.exp_ne_zero _)

theorem exp_one_le_rSec {L : LocPot X} {s : X → X → ℂ}
    (hle : ∀ y, ‖s y y‖ * Real.exp (-L.φ y y) ≤ 1) (y : X) : Real.exp 1 ≤ rSec L s y := by
  have h : logNormSec L s y ≤ 0 :=
    Real.log_nonpos (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le) (hle y)
  unfold rSec
  linarith

theorem LemmaETailLog.proof (h₁ : LemmaETailMass.Statement) (h₂ : TailLogOfMass.Statement) :
    LemmaETailLog.Statement := by
  intro X _ _ _ D A Om L s hL hs hd hle C₁ hC₁
  obtain ⟨CE, hCE⟩ := h₁ D A Om L s hL hs hd hle C₁ hC₁
  refine ⟨shellConst D * CE, fun u hu => ?_⟩
  exact h₂ D A (secOpen s) (rSec L s) Om.pot u (isOpen_secOpen hL hs) (continuousOn_rSec hL hs)
    (fun y _ => exp_one_le_rSec hle y) Om.isPot (fun i => (hu i).smooth) (fun i => (hu i).nonneg) CE
    (hCE u hu)

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PListProductMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory Filter Topology
open ReciprocityTheory.AnForm (levi levi_add_smul)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPsh mInt maMeasure isPotentialAdd
  isPotentialRsmul isPotential_ofFun isPshAdd maMeasureMono maMeasure_thm massIndep mIntegrableCont
  pot_contDiffAt_two)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

variable {D : ℕ} {X : Type} [TopologicalSpace X]

theorem isPsh_of_formNonneg {A : FinHolAtlas D X} {V : Set X} (hV : interior Vᶜ = ∅)
    {P : LocPot X} (hP : IsPotential A P) (hnn : FormNonneg A V P) : IsPsh A P := by
  intro x j y hy w
  by_contra hneg
  push Not at hneg
  have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x) :=
    (A.chart j).isOpen_inter_preimage_symm (P.isOpen_U x)
  have h2 := pot_contDiffAt_two hP x j hy.1 hy.2
  have hc : ContinuousAt (fun z => levi (P.φ x ∘ (A.chart j).symm) z w) y := by
    have h0 := ((h2.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0)
      (by norm_num)).continuousAt
    unfold levi
    exact (((h0.clm_apply continuousAt_const).clm_apply continuousAt_const).add
      ((h0.clm_apply continuousAt_const).clm_apply continuousAt_const)).div_const 4
  have hev : ∀ᶠ z in 𝓝 y, levi (P.φ x ∘ (A.chart j).symm) z w < 0 ∧
      z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x :=
    (hc.eventually (eventually_lt_nhds hneg)).and (hO.mem_nhds hy)
  obtain ⟨N, hNsub, hNo, hyN⟩ := mem_nhds_iff.1 hev
  have himg : IsOpen ((A.chart j).symm '' N) :=
    (A.chart j).isOpen_image_symm_of_subset_target hNo fun z hz => (hNsub hz).2.1
  have hsub : (A.chart j).symm '' N ⊆ Vᶜ := by
    rintro _ ⟨z, hz, rfl⟩ hzV
    have h := hnn x j z ⟨(hNsub hz).2.1, hzV, (hNsub hz).2.2⟩ w
    linarith [(hNsub hz).1]
  have hmem : (A.chart j).symm y ∈ interior Vᶜ := interior_maximal hsub himg ⟨y, hyN, rfl⟩
  rw [hV] at hmem
  exact hmem

end GroundTheory.Heights₂.Heights.AnalyticLimit
end
