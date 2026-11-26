module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfH

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfJ
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfI
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OntoI

open NumberField Complex Matrix Topology Filter MeasureTheory Set ReciprocityTheory.ChartRestriction.G.FD
  ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB
  ReciprocityTheory.ChartRestriction.G.AR.Up.OntoH
open scoped ComplexConjugate ContDiff ENNReal InnerProductSpace

noncomputable section

theorem sq_add_le (a b : ℂ) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h1 : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

theorem lint_add_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {a b : α → ℂ} {k : α → ℝ}
    (hk : ∀ x, 0 < k x) {om : α → ℝ≥0∞}
    (ha : AEMeasurable (fun x => ENNReal.ofReal (‖a x‖ ^ 2 / k x) * om x) μ) :
    ∫⁻ x, ENNReal.ofReal (‖a x + b x‖ ^ 2 / k x) * om x ∂μ ≤
      2 * ∫⁻ x, ENNReal.ofReal (‖a x‖ ^ 2 / k x) * om x ∂μ +
        2 * ∫⁻ x, ENNReal.ofReal (‖b x‖ ^ 2 / k x) * om x ∂μ := by
  calc ∫⁻ x, ENNReal.ofReal (‖a x + b x‖ ^ 2 / k x) * om x ∂μ
      ≤ ∫⁻ x, (2 * (ENNReal.ofReal (‖a x‖ ^ 2 / k x) * om x) +
          2 * (ENNReal.ofReal (‖b x‖ ^ 2 / k x) * om x)) ∂μ := by
        refine lintegral_mono fun x => ?_
        have hk' := hk x
        have hA : 0 ≤ ‖a x‖ ^ 2 / k x := div_nonneg (sq_nonneg _) hk'.le
        have hB : 0 ≤ ‖b x‖ ^ 2 / k x := div_nonneg (sq_nonneg _) hk'.le
        have h1 : ‖a x + b x‖ ^ 2 / k x ≤ 2 * (‖a x‖ ^ 2 / k x) + 2 * (‖b x‖ ^ 2 / k x) := by
          rw [← mul_div_assoc, ← mul_div_assoc, ← add_div]
          exact div_le_div_of_nonneg_right (sq_add_le _ _) hk'.le
        calc ENNReal.ofReal (‖a x + b x‖ ^ 2 / k x) * om x
            ≤ ENNReal.ofReal (2 * (‖a x‖ ^ 2 / k x) + 2 * (‖b x‖ ^ 2 / k x)) * om x := by
              gcongr
          _ = 2 * (ENNReal.ofReal (‖a x‖ ^ 2 / k x) * om x) +
                2 * (ENNReal.ofReal (‖b x‖ ^ 2 / k x) * om x) := by
              rw [ENNReal.ofReal_add (mul_nonneg zero_le_two hA) (mul_nonneg zero_le_two hB),
                ENNReal.ofReal_mul (zero_le_two : (0 : ℝ) ≤ 2),
                ENNReal.ofReal_mul (zero_le_two : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
              ring
    _ = 2 * ∫⁻ x, ENNReal.ofReal (‖a x‖ ^ 2 / k x) * om x ∂μ +
          2 * ∫⁻ x, ENNReal.ofReal (‖b x‖ ^ 2 / k x) * om x ∂μ := by
        rw [lintegral_add_left' (ha.const_mul 2), lintegral_const_mul' _ _ ENNReal.ofNat_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r)

theorem pnorm_sub_le (la : Wt X.Ψ r) (f g : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    X.pnorm la (fun y => f y - g y) x ≤ X.pnorm la f x + X.pnorm la g x := by
  unfold Data.pnorm
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_sub_le _ _)
    (Finset.prod_nonneg fun τ _ => Finset.prod_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _)

theorem bdd_sub {la : Wt X.Ψ r} {f g : Frame X.Ψ r → ℂ} (hf : X.IsBddSec la f) (hg : X.IsBddSec la g) :
    X.IsBddSec la (fun y => f y - g y) := by
  obtain ⟨hf1, C1, hC1⟩ := hf
  obtain ⟨hg1, C2, hC2⟩ := hg
  refine ⟨?_, C1 + C2, fun x hx => (pnorm_sub_le X la f g x).trans (add_le_add (hC1 x hx) (hC2 x hx))⟩
  unfold Data.IsSec at hf1 hg1 ⊢
  obtain ⟨hd1, hb1, hl1⟩ := hf1
  obtain ⟨hd2, hb2, hl2⟩ := hg1
  refine ⟨hd1.sub hd2, fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩
  · simp only [hb1 x hx b hb, hb2 x hx b hb]
    ring
  · simp only [hl1 γ hγ x hx, hl2 γ hγ x hx]
    ring

theorem poin_add (la : Wt X.Ψ r) {P1 P2 : Frame X.Ψ r → ℂ} {x : Frame X.Ψ r}
    (h1 : Summable fun γ : X.Γ => ‖(X.χ la γ.1)⁻¹ * P1 (lact γ.1 x)‖)
    (h2 : Summable fun γ : X.Γ => ‖(X.χ la γ.1)⁻¹ * P2 (lact γ.1 x)‖) :
    poin X la (fun y => P1 y + P2 y) x = poin X la P1 x + poin X la P2 x := by
  unfold poin
  rw [← Summable.tsum_add h1.of_norm h2.of_norm]
  congr 1
  funext γ
  ring

theorem poin_smul (la : Wt X.Ψ r) (a : ℂ) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    poin X la (fun y => a * P y) x = a * poin X la P x := by
  unfold poin
  rw [← tsum_mul_left]
  congr 1
  funext γ
  ring

theorem poin_zero (la : Wt X.Ψ r) (x : Frame X.Ψ r) : poin X la (fun _ => 0) x = 0 := by
  simp [poin]

variable (W : Frame X.Ψ r → ℝ≥0∞) (FF : Set (V (nd X)))

def nuF : Measure (V (nd X)) :=
  ((muF X x0).restrict FF).withDensity fun z => ENNReal.ofReal (W (cpt X x0 z)).toReal

variable {X x0 W FF}

private lemma measurable_cpt : Measurable (cpt X x0) := by
  refine Measurable.of_eval fun τ => Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  simp only [cpt, rmul, mat, nmat, Matrix.mul_apply, Matrix.of_apply]
  refine Finset.measurable_sum _ fun c _ => ?_
  split_ifs
  · refine Measurable.const_mul ?_ _
    first
      | exact measurable_pi_apply _
      | exact (EuclideanSpace.proj _).continuous.measurable
      | fun_prop
  · exact measurable_const
  · exact measurable_const

theorem dens_meas (hW : Measurable W) :
    Measurable fun z => ENNReal.ofReal (W (cpt X x0 z)).toReal :=
  (hW.comp measurable_cpt).ennreal_toReal.ennreal_ofReal

theorem nuF_ac : nuF X x0 W FF ≪ muF X x0 := by
  unfold nuF
  exact (withDensity_absolutelyContinuous _ _).trans
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)

private lemma measurableSet_dom' : MeasurableSet X.dom := by
  have hc : ∀ (τ : X.Ψ) (i : Fin (r + 1)), Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i := by
    intro τ i
    unfold dmin lminor ReciprocityTheory.ChartRestriction.G.FD.gram hermC ReciprocityTheory.ChartRestriction.G.FD.col mat
    fun_prop
  have hd : ∀ τ : X.Ψ, Continuous fun x : Frame X.Ψ r => (mat x τ).det := fun τ =>
    Continuous.matrix_det (A := fun x : Frame X.Ψ r => mat x τ) (continuous_apply τ)
  have ho : IsOpen X.dom := by
    show IsOpen {x : Frame X.Ψ r | ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧
      ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re}
    simp only [Set.setOf_forall, Set.setOf_and]
    exact isOpen_iInter_of_finite fun τ => (isOpen_ne_fun (hd τ) continuous_const).inter
      (isOpen_iInter_of_finite fun i =>
        isOpen_lt continuous_const (continuous_const.mul (Complex.continuous_re.comp (hc τ i))))
  exact ho.measurableSet

theorem memLp_of (hW : Measurable W) {h : Frame X.Ψ r → ℂ} (hh : ContinuousOn h X.dom)
    (hF : InFF X x0 W FF h) : MemLp (fun z => h (cpt X x0 z)) 2 (nuF X x0 W FF) := by
  classical
  unfold InFF at hF
  have hOm : MeasurableSet (OmF X x0) := measurable_cpt measurableSet_dom'
  have hae : ∀ᵐ z ∂nuF X x0 W FF, z ∈ OmF X x0 := by
    have h1 : ∀ᵐ z ∂muF X x0, z ∈ OmF X x0 := by
      unfold muF
      exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hOm)
    exact nuF_ac.ae_le h1
  have hg : Measurable (X.dom.piecewise h 0) :=
    ContinuousOn.measurable_piecewise hh continuous_const.continuousOn measurableSet_dom'
  have hm : AEStronglyMeasurable (fun z => h (cpt X x0 z)) (nuF X x0 W FF) := by
    have hm0 : Measurable fun z => X.dom.piecewise h 0 (cpt X x0 z) := hg.comp measurable_cpt
    refine hm0.aestronglyMeasurable.congr ?_
    filter_upwards [hae] with z hz
    exact Set.piecewise_eq_of_mem _ _ _ hz
  refine (memLp_two_iff_integrable_sq_norm hm).2 ⟨hm.norm.pow 2, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun z => by
    simp only [Pi.zero_apply]
    positivity)]
  refine lt_of_le_of_lt ?_ hF
  unfold nuF
  refine (lintegral_withDensity_le_lintegral_mul _ (dens_meas hW) _).trans (lintegral_mono fun z => ?_)
  simp only [Pi.mul_apply]
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left ENNReal.ofReal_toReal_le zero_le

theorem integral_nu (hW : Measurable W) (g : V (nd X) → ℂ) :
    ∫ z, g z ∂nuF X x0 W FF = ∫ z in FF, g z * ((W (cpt X x0 z)).toReal : ℂ) ∂muF X x0 := by
  unfold nuF
  rw [integral_withDensity_eq_integral_toReal_smul (dens_meas hW)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  funext z
  rw [ENNReal.toReal_ofReal ENNReal.toReal_nonneg, Complex.real_smul, mul_comm]

theorem inner_toLp (hW : Measurable W) {a b : V (nd X) → ℂ} (ha : MemLp a 2 (nuF X x0 W FF))
    (hb : MemLp b 2 (nuF X x0 W FF)) :
    ⟪ha.toLp a, hb.toLp b⟫_ℂ = ∫ z in FF, conj (a z) * b z * ((W (cpt X x0 z)).toReal : ℂ) ∂muF X x0 := by
  rw [MeasureTheory.L2.inner_def]
  have h : ∀ᵐ z ∂nuF X x0 W FF, ⟪(ha.toLp a) z, (hb.toLp b) z⟫_ℂ = conj (a z) * b z := by
    filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with z h1 h2
    rw [h1, h2]
    simp [RCLike.inner_apply] <;> ring
  rw [integral_congr_ae h, integral_nu hW]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OntoI
end

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField Complex Matrix Topology Filter MeasureTheory Set ReciprocityTheory.ChartRestriction.G.FD
  ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB ReciprocityTheory.ChartRestriction.G.AR.Up.OntoH
  ReciprocityTheory.ChartRestriction.G.AR.Up.OntoI
open scoped ComplexConjugate ContDiff ENNReal InnerProductSpace

noncomputable section

namespace OntoJ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def Dt (X : Data E r) (x0 : Frame X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ) (la : Wt X.Ψ r)
    (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ) : Prop :=
  DifferentiableOn ℂ F (OmF X x0) ∧ InAt X x0 W bb F ∧ IsBEq X la P ∧
    ∀ z ∈ OmF X x0, P (cpt X x0 z) = F z


open Classical in
def TL {α : Type*} [MeasurableSpace α] (ν : Measure α) (f : α → ℂ) : Lp ℂ 2 ν :=
  if h : MemLp f 2 ν then h.toLp f else 0

section TLs

variable {α : Type*} [MeasurableSpace α] {ν : Measure α}

theorem TL_eq {f : α → ℂ} (h : MemLp f 2 ν) : TL ν f = h.toLp f := by
  unfold TL
  rw [dite_eq_left h]

theorem TL_congr {f g : α → ℂ} (hf : MemLp f 2 ν) (hfg : f =ᵐ[ν] g) : TL ν f = TL ν g := by
  rw [TL_eq hf, TL_eq (hf.ae_eq hfg)]
  exact (MemLp.toLp_eq_toLp_iff _ _).2 hfg

theorem TL_add {f g : α → ℂ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    TL ν (f + g) = TL ν f + TL ν g := by
  rw [TL_eq (hf.add hg), TL_eq hf, TL_eq hg]
  exact MemLp.toLp_add hf hg

theorem TL_sub {f g : α → ℂ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    TL ν (f - g) = TL ν f - TL ν g := by
  rw [TL_eq (hf.sub hg), TL_eq hf, TL_eq hg]
  exact MemLp.toLp_sub hf hg

theorem TL_smul {f : α → ℂ} (a : ℂ) (hf : MemLp f 2 ν) : TL ν (a • f) = a • TL ν f := by
  rw [TL_eq (hf.const_smul a), TL_eq hf]
  exact MemLp.toLp_const_smul a hf

theorem TL_zero : TL ν (0 : α → ℂ) = 0 := by
  rw [TL_eq MeasureTheory.MemLp.zero]
  exact MemLp.toLp_zero _

end TLs

variable (X : Data E r) (x0 : Frame X.Ψ r) {W : Frame X.Ψ r → ℝ≥0∞} {bb : ℝ} {la : Wt X.Ψ r}

theorem ka_cont : ContinuousOn (kaF X x0 bb) (OmF X x0) :=
  fun _ hz => (ka_contDiffAt bb hz).continuousAt.continuousWithinAt

theorem aemF (hWm : Measurable W) {F : V (nd X) → ℂ} (hF : ContinuousOn F (OmF X x0)) :
    AEMeasurable (fun z => ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x0 bb z) * W (cpt X x0 z)) (muF X x0) := by
  have h1 : ContinuousOn (fun z => ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x0 bb z)) (OmF X x0) :=
    ENNReal.continuous_ofReal.comp_continuousOn
      ((hF.norm.pow 2).div (ka_cont X x0) fun z _ => (Real.exp_pos _).ne')
  have h2 : Measurable fun z => W (cpt X x0 z) := hWm.comp (cd_cpt X x0).continuous.measurable
  have h3 : AEMeasurable (fun z => ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x0 bb z) * W (cpt X x0 z))
      (volume.restrict (OmF X x0)) :=
    (h1.aemeasurable (isOpen_OmF X x0).measurableSet).mul h2.aemeasurable
  exact h3.mono_ac (withDensity_absolutelyContinuous _ _)

theorem Dt_zero : Dt X x0 W bb la (fun _ => 0) (fun _ => 0) := by
  refine ⟨differentiableOn_const _, ?_, ⟨differentiableOn_const _, fun _ _ _ _ => by simp⟩, fun _ _ => rfl⟩
  unfold InAt
  simp

theorem Dt_add (hWm : Measurable W) {F1 F2 : V (nd X) → ℂ} {P1 P2 : Frame X.Ψ r → ℂ}
    (h1 : Dt X x0 W bb la F1 P1) (h2 : Dt X x0 W bb la F2 P2) :
    Dt X x0 W bb la (fun z => F1 z + F2 z) (fun y => P1 y + P2 y) := by
  refine ⟨h1.1.add h2.1, ?_, ⟨h1.2.2.1.1.add h2.2.2.1.1, fun x hx b hb => ?_⟩, fun z hz => ?_⟩
  · unfold InAt
    refine lt_of_le_of_lt (lint_add_le (k := kaF X x0 bb) (fun z => Real.exp_pos _)
      (aemF X x0 hWm h1.1.continuousOn)) ?_
    exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by simp) h1.2.1, ENNReal.mul_lt_top (by simp) h2.2.1⟩
  · beta_reduce
    rw [h1.2.2.1.2 x hx b hb, h2.2.2.1.2 x hx b hb]
    ring
  · beta_reduce
    rw [h1.2.2.2 z hz, h2.2.2.2 z hz]

theorem Dt_smul (a : ℂ) {F : V (nd X) → ℂ} {P : Frame X.Ψ r → ℂ} (h : Dt X x0 W bb la F P) :
    Dt X x0 W bb la (fun z => a * F z) (fun y => a * P y) := by
  refine ⟨h.1.const_mul a, ?_, ⟨h.2.2.1.1.const_mul a, fun x hx b hb => ?_⟩, fun z hz => ?_⟩
  · have heq : ∀ z, ENNReal.ofReal (‖a * F z‖ ^ 2 / kaF X x0 bb z) * W (cpt X x0 z) =
        ENNReal.ofReal (‖a‖ ^ 2) * (ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x0 bb z) * W (cpt X x0 z)) := by
      intro z
      rw [norm_mul, mul_pow, mul_div_assoc, ENNReal.ofReal_mul (by positivity), mul_assoc]
    unfold InAt
    simp_rw [heq]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top h.2.1
  · beta_reduce
    rw [h.2.2.1.2 x hx b hb]
    ring
  · beta_reduce
    rw [h.2.2.2 z hz]

end OntoJ

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField Complex Matrix Topology Filter MeasureTheory Set ReciprocityTheory.ChartRestriction.G.FD
  ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB ReciprocityTheory.ChartRestriction.G.AR.Up.OntoH
  ReciprocityTheory.ChartRestriction.G.AR.Up.OntoI ReciprocityTheory.ChartRestriction.G.AR.Up.OntoJ
open scoped ComplexConjugate ContDiff ENNReal InnerProductSpace

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem onto_of (hPoin : PoinStatement (E := E)) (hExtF : ExtFStatement (E := E))
    (hGrad : RhGradFStatement (E := E)) (hExG : ExhaustGStatement (E := E))
    (hKa : KaUnfoldStatement (E := E)) (hPair : PairUnfoldStatement (E := E))
    (hBig : BigCellStatement (E := E)) (hConn : OmFConnStatement (E := E)) :
    OntoStatement (E := E) := by
  intro r X x0 hx0 hPD la W Ps g1 bb m hW hWL hbb4 hm hg1 hg1ne hPs hWPs hLev hSS FF hFF hfin
    f hf hfF
  obtain ⟨K, g, hg⟩ := hfin
  have hWm : Measurable W := hW.1
  have hPo := fun (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ)
      (hD : OntoJ.Dt X x0 W bb la F P) =>
    hPoin r X x0 hx0 hPD la W bb hW hWL hbb4 F P hD.1 hD.2.1 hD.2.2.1 hD.2.2.2
  have hae : ∀ᵐ z ∂(OntoI.nuF X x0 W FF), z ∈ FF := by
    have h1 : ∀ᵐ z ∂((muF X x0).restrict FF), z ∈ FF := ae_restrict_mem hFF.1
    first
      | exact (withDensity_absolutelyContinuous _ _).ae_le h1
      | (unfold OntoI.nuF; exact (withDensity_absolutelyContinuous _ _).ae_le h1)
  have hmemP : ∀ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), OntoJ.Dt X x0 W bb la F P →
      MemLp (fun z => poin X la P (cpt X x0 z)) 2 (OntoI.nuF X x0 W FF) := fun F P hD =>
    OntoI.memLp_of (r := r) (X := X) (x0 := x0) (W := W) (FF := FF) hWm
      (hPo F P hD).2.1.1.1.continuousOn ((hPo F P hD).2.2.1 FF hFF)
  have hmemf : MemLp (fun z => f (cpt X x0 z)) 2 (OntoI.nuF X x0 W FF) :=
    OntoI.memLp_of (r := r) (X := X) (x0 := x0) (W := W) (FF := FF) hWm
      hf.1.1.1.continuousOn hfF
  have hzero : MemLp (fun z => (0 : Frame X.Ψ r → ℂ) (cpt X x0 z)) 2 (OntoI.nuF X x0 W FF) := by
    refine (hmemP _ _ (OntoJ.Dt_zero X x0)).ae_eq (ae_of_all _ fun z => ?_)
    exact OntoI.poin_zero (r := r) (X := X) la _

  obtain ⟨M, hMmem⟩ : ∃ M : Submodule ℂ (Lp ℂ 2 (OntoI.nuF X x0 W FF)), ∀ v, v ∈ M ↔
      ∃ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ) (hD : OntoJ.Dt X x0 W bb la F P),
        v = (hmemP F P hD).toLp _ := by
    refine ⟨{ carrier := {v | ∃ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ)
                (hD : OntoJ.Dt X x0 W bb la F P), v = (hmemP F P hD).toLp _}
              add_mem' := by
                rintro _ _ ⟨F1, P1, hD1, rfl⟩ ⟨F2, P2, hD2, rfl⟩
                refine ⟨_, _, OntoJ.Dt_add (r := r) (X := X) (x0 := x0) hWm hD1 hD2, ?_⟩
                rw [← MemLp.toLp_add (hmemP F1 P1 hD1) (hmemP F2 P2 hD2)]
                refine MemLp.toLp_congr _ _ ?_
                filter_upwards [hae] with z hz
                have hx : cpt X x0 z ∈ X.dom := hFF.2.1 hz
                show poin X la P1 (cpt X x0 z) + poin X la P2 (cpt X x0 z) =
                  poin X la (fun y => P1 y + P2 y) (cpt X x0 z)
                exact (OntoI.poin_add (r := r) (X := X) la ((hPo F1 P1 hD1).1 _ hx)
                  ((hPo F2 P2 hD2).1 _ hx)).symm
              zero_mem' := ⟨fun _ => 0, fun _ => 0, OntoJ.Dt_zero X x0, by
                rw [← MemLp.toLp_zero hzero]
                exact MemLp.toLp_congr _ _
                  (ae_of_all _ fun z => (OntoI.poin_zero (r := r) (X := X) la (cpt X x0 z)).symm)⟩
              smul_mem' := by
                rintro a _ ⟨F, P, hD, rfl⟩
                refine ⟨_, _, OntoJ.Dt_smul (r := r) (X := X) (x0 := x0) a hD, ?_⟩
                rw [← MemLp.toLp_const_smul a (hmemP F P hD)]
                exact MemLp.toLp_congr _ _
                  (ae_of_all _ fun z => (OntoI.poin_smul (r := r) (X := X) la a P (cpt X x0 z)).symm) },
      fun v => Iff.rfl⟩

  obtain ⟨D2, hD2i⟩ : ∃ D2 : Submodule ℂ (Frame X.Ψ r → ℂ), ∀ h, h ∈ D2 ↔
      h ∈ Submodule.span ℂ (Set.range g) ∧
        MemLp (fun z => h (cpt X x0 z)) 2 (OntoI.nuF X x0 W FF) :=
    ⟨{ carrier := {h | h ∈ Submodule.span ℂ (Set.range g) ∧
          MemLp (fun z => h (cpt X x0 z)) 2 (OntoI.nuF X x0 W FF)}
       add_mem' := fun {a b} ha hb => ⟨Submodule.add_mem _ ha.1 hb.1, ha.2.add hb.2⟩
       zero_mem' := ⟨Submodule.zero_mem _, hzero⟩
       smul_mem' := fun c {h} hh => ⟨Submodule.smul_mem _ c hh.1, hh.2.const_smul c⟩ },
      fun h => Iff.rfl⟩
  have hD2m : ∀ h : D2, MemLp (fun z => (h : Frame X.Ψ r → ℂ) (cpt X x0 z)) 2
      (OntoI.nuF X x0 W FF) := fun h => ((hD2i h).1 h.2).2
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : D2 →ₗ[ℂ] Lp ℂ 2 (OntoI.nuF X x0 W FF), ∀ h : D2,
      Φ h = (hD2m h).toLp _ :=
    ⟨{ toFun := fun h => (hD2m h).toLp _
       map_add' := fun a b => MemLp.toLp_add (hD2m a) (hD2m b)
       map_smul' := fun c a => MemLp.toLp_const_smul c (hD2m a) }, fun h => rfl⟩
  have hMle : M ≤ LinearMap.range Φ := by
    intro v hv
    obtain ⟨F, P, hD, rfl⟩ := (hMmem v).1 hv
    obtain ⟨c, hc⟩ := hg _ (hSS _ (hPo F P hD).2.1) ((hPo F P hD).2.2.1 FF hFF)
    obtain ⟨h, hhD, hhx⟩ : ∃ h : Frame X.Ψ r → ℂ, h ∈ Submodule.span ℂ (Set.range g) ∧
        ∀ x, h x = ∑ i, c i * g i x :=
      ⟨∑ i, c i • g i, Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i)),
        fun x => by simp [Finset.sum_apply]⟩
    have hae2 : (fun z => h (cpt X x0 z)) =ᵐ[OntoI.nuF X x0 W FF]
        fun z => poin X la P (cpt X x0 z) := by
      filter_upwards [hae] with z hz
      rw [hhx, hc _ (hFF.2.1 hz)]
    have hmh : MemLp (fun z => h (cpt X x0 z)) 2 (OntoI.nuF X x0 W FF) :=
      (hmemP F P hD).ae_eq hae2.symm
    refine LinearMap.mem_range.2 ⟨⟨h, (hD2i h).2 ⟨hhD, hmh⟩⟩, ?_⟩
    rw [hΦ]
    exact MemLp.toLp_congr _ _ hae2
  haveI hfS : FiniteDimensional ℂ (Submodule.span ℂ (Set.range g)) := by
    first
      | exact FiniteDimensional.span_of_finite ℂ (Set.finite_range g)
      | exact FiniteDimensional.span_of_finite (Set.finite_range g)
      | exact Module.Finite.iff_fg.mpr (Submodule.fg_span (Set.finite_range g))
      | exact inferInstance
  have hD2le : D2 ≤ Submodule.span ℂ (Set.range g) := by
    intro h hh
    exact ((hD2i h).1 hh).1
  haveI hfD2 : FiniteDimensional ℂ D2 := by
    first
      | exact Submodule.finiteDimensional_of_le hD2le
      | exact Module.Finite.of_injective (Submodule.inclusion hD2le)
          (Submodule.inclusion_injective hD2le)
  haveI hfR : FiniteDimensional ℂ (LinearMap.range Φ) := by
    first
      | exact LinearMap.finiteDimensional_range Φ
      | exact inferInstance
  haveI hfM : FiniteDimensional ℂ M := by
    first
      | exact Submodule.finiteDimensional_of_le hMle
      | exact Module.Finite.of_injective (Submodule.inclusion hMle)
          (Submodule.inclusion_injective hMle)
  haveI : CompleteSpace M := by
    first
      | exact FiniteDimensional.complete ℂ M
      | exact inferInstance

  obtain ⟨y, hyM, w, hw, hvyw⟩ : ∃ y ∈ M, ∃ w ∈ M.orthogonal,
      hmemf.toLp _ = y + w := by
    first
      | exact Submodule.exists_add_mem_mem_orthogonal M _
      | exact Submodule.exists_add_mem_mem_orthogonal _
  obtain ⟨F, P, hD, rfl⟩ := (hMmem y).1 hyM
  have hmemf0 : MemLp (fun z => f (cpt X x0 z) - poin X la P (cpt X x0 z)) 2
      (OntoI.nuF X x0 W FF) := hmemf.sub (hmemP F P hD)
  have hwLp : w = hmemf0.toLp _ := by
    change w = (hmemf.sub (hmemP F P hD)).toLp _
    rw [MemLp.toLp_sub hmemf (hmemP F P hD), hvyw]
    abel
  have horth : ∀ (F' : V (nd X) → ℂ) (P' : Frame X.Ψ r → ℂ), DifferentiableOn ℂ F' (OmF X x0) →
      InAt X x0 W bb F' → IsBEq X la P' → (∀ z ∈ OmF X x0, P' (cpt X x0 z) = F' z) →
      ∫ z in FF, poin X la P' (cpt X x0 z) *
          (starRingEnd ℂ) (f (cpt X x0 z) - poin X la P (cpt X x0 z)) *
          ((W (cpt X x0 z)).toReal : ℂ) ∂muF X x0 = 0 := by
    intro F' P' h1 h2 h3 h4
    have hD' : OntoJ.Dt X x0 W bb la F' P' := ⟨h1, h2, h3, h4⟩
    have hmem' : (hmemP F' P' hD').toLp _ ∈ M :=
      (hMmem _).2 ⟨F', P', hD', rfl⟩
    have h0 : ⟪(hmemP F' P' hD').toLp _, w⟫_ℂ = 0 := by
      first
        | exact Submodule.inner_right_of_mem_orthogonal hmem' hw
        | exact (Submodule.mem_orthogonal M w).1 hw _ hmem'
    have h0' : ⟪w, (hmemP F' P' hD').toLp _⟫_ℂ = 0 := by
      first
        | exact inner_eq_zero_symm.1 h0
        | exact Submodule.inner_left_of_mem_orthogonal hmem' hw
    rw [hwLp,
      OntoI.inner_toLp (r := r) (X := X) (x0 := x0) (W := W) (FF := FF) hWm hmemf0
        (hmemP F' P' hD')] at h0'
    refine (integral_congr_ae ?_).trans h0'
    filter_upwards with z
    ring
  have hf0SS : (fun y => f y - poin X la P y) ∈ X.SS la :=
    hSS _ (OntoI.bdd_sub (r := r) (X := X) hf.1 (hPo F P hD).2.1)
  have hff0 : InFF X x0 W FF (fun y => f y - poin X la P y) := by
    have hcf : ContinuousOn (fun z => f (cpt X x0 z)) (OmF X x0) :=
      hf.1.1.1.continuousOn.comp
        ((OntoB.cd_cpt (r := r) (X := X) (x0 := x0)).continuous.continuousOn)
        (by intro z hz; exact hz)
    have h1 : AEMeasurable (fun z => ENNReal.ofReal (‖f (cpt X x0 z)‖ ^ 2 / (1 : ℝ))) (muF X x0) :=
      OntoH.aem_of (r := r) (X := X) (x0 := x0)
        (ENNReal.continuous_ofReal.comp_continuousOn ((hcf.norm.pow 2).div_const 1))
    have haem : AEMeasurable
        (fun z => ENNReal.ofReal (‖f (cpt X x0 z)‖ ^ 2 / (1 : ℝ)) * W (cpt X x0 z))
        ((muF X x0).restrict FF) :=
      (h1.mul (OntoH.measW (r := r) (X := X) (x0 := x0) hWm).aemeasurable).restrict
    have key := OntoI.lint_add_le (μ := (muF X x0).restrict FF) (a := fun z => f (cpt X x0 z))
      (b := fun z => -poin X la P (cpt X x0 z)) (k := fun _ => (1 : ℝ))
      (om := fun z => W (cpt X x0 z)) (fun _ => one_pos) haem
    simp only [div_one, norm_neg, ← sub_eq_add_neg] at key
    have hPF := (hPo F P hD).2.2.1 FF hFF
    show ∫⁻ z in FF, ENNReal.ofReal (‖f (cpt X x0 z) - poin X la P (cpt X x0 z)‖ ^ 2) *
      W (cpt X x0 z) ∂muF X x0 < ⊤
    refine lt_of_le_of_lt key (ENNReal.add_lt_top.2 ⟨?_, ?_⟩)
    · first
        | exact ENNReal.mul_lt_top (by simp) hfF
        | exact ENNReal.mul_lt_top (by simp) hfF.ne
    · first
        | exact ENNReal.mul_lt_top (by simp) hPF
        | exact ENNReal.mul_lt_top (by simp) hPF.ne
  have hvan := OntoH.vanish (r := r) (X := X) (x0 := x0) hExG hGrad hKa hPair hBig hConn hExtF
    hx0 hPD hW hWL hbb4 hm hg1 hg1ne hPs hWPs hLev hFF hf0SS hff0 horth
  obtain ⟨hD1, hD2, hD3, hD4⟩ := hD
  refine ⟨F, P, hD1, hD2, hD3, hD4, fun x hx => ?_⟩
  have hx0' := hvan x hx
  exact (sub_eq_zero.1 hx0').symm

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
