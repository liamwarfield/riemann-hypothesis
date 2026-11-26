module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.SigIntIntegrable
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvGroup

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.MinorsOnOfDD
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.BeIntIntegrableOf
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.TopH

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

def MinorsOn (D : RealPlaceData k r Wp Wp) (X : SigData k r) : Prop :=
  ∀ u₁ ∈ Vfl X, ∀ u₂ ∈ Vfl X, ∀ u₃ ∈ Vfl X, ∀ u₄ ∈ Vfl X, ∀ e₁ e₂ e₃ e₄ : Wp,
    ⟪e₁, beOp D X u₁ u₂ e₂⟫_ℂ * ⟪e₃, beOp D X u₃ u₄ e₄⟫_ℂ =
      ⟪e₁, beOp D X u₁ u₄ e₄⟫_ℂ * ⟪e₃, beOp D X u₃ u₂ e₂⟫_ℂ

lemma beInt_add_left (D : RealPlaceData k r Wp Wp) (X : SigData k r) (u v u' : X.Hs) (p : Mt k r × Mt k r) :
    beInt D X (u + v) u' p = beInt D X u u' p + beInt D X v u' p := by
  simp only [beInt, mc, map_add (f := _), inner_add_right, add_mul, add_smul]

lemma beInt_smul_left (D : RealPlaceData k r Wp Wp) (X : SigData k r) (c : ℂ) (u u' : X.Hs)
    (p : Mt k r × Mt k r) : beInt D X (c • u) u' p = c • beInt D X u u' p := by
  simp only [beInt, mc, map_smul, inner_smul_right, smul_smul, mul_assoc]

theorem beInt_integrable_of (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hD : IsDiag D) (hX : SqIntG D X)
    (ha : aM k r ≤ X.a) (h0 : StSchurG) (h1 : StPairs) (h1' : StBeConv) :
    ∀ u ∈ Vfl X, ∀ u' ∈ Vfl X, Integrable (beInt D X u u') (D.μW.prod D.μN) := by
  intro u hu u' hu'
  obtain ⟨d, hd⟩ := h0 k r Wp D X hD hX
  obtain ⟨C, hC⟩ := h1 k r Wp D X hD hX d hd X.a X.a u hu u' hu'
  refine h1' k r Wp D X hD hX (X.a - AG k r - 1) ?_ u u' ⟨C, ?_⟩
  · have hn : (1 : ℝ) ≤ nR k r := by
      unfold nR
      exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)
    unfold AS AG
    unfold aM at ha
    nlinarith [mul_nonneg (sub_nonneg.2 hn) (by positivity : (0 : ℝ) ≤ 3 * nR k r ^ 2 + 2 * nR k r + 2)]
  · simpa [min_self] using hC

theorem multOne_of_minors (D : RealPlaceData k r Wp Wp) (X : SigData k r)
    (hH : ∀ u ∈ Vfl X, ∀ u' ∈ Vfl X, ∀ η ξ : Wp, ⟪ξ, beOp D X u u' η⟫_ℂ = ⟪beOp D X u' u ξ, η⟫_ℂ)
    (hP : ∀ u ∈ Vfl X, ∀ ξ : Wp, 0 ≤ (⟪ξ, beOp D X u u ξ⟫_ℂ).re)
    (hInt : ∀ u ∈ Vfl X, ∀ u' ∈ Vfl X, Integrable (beInt D X u u') (D.μW.prod D.μN))
    (hEq : ∀ u ∈ Vfl X, ∀ u' ∈ Vfl X, ∀ h ∈ UWset k r D.z, ∀ m ∈ Nset k r,
        beOp D X (X.σ (m * h) u) u' = psiD D m • (D.π h).comp (beOp D X u u'))
    (hM : MinorsOn D X) : ∃ l : X.Hs → Wp, IsMultOneMap D X l := by
  have hre : ∀ u ∈ Vfl X, ∀ ξ : Wp, ⟪ξ, beOp D X u u ξ⟫_ℂ = ((⟪ξ, beOp D X u u ξ⟫_ℂ).re : ℂ) := by
    intro u hu ξ
    have h1 := hH u hu u hu ξ ξ
    have h2 : starRingEnd ℂ ⟪ξ, beOp D X u u ξ⟫_ℂ = ⟪ξ, beOp D X u u ξ⟫_ℂ := by
      rw [inner_conj_symm]; exact h1.symm
    exact (Complex.conj_eq_iff_re.mp h2).symm
  by_cases h0 : ∃ v₀ ∈ Vfl X, ∃ ξ₀ : Wp, 0 < (⟪ξ₀, beOp D X v₀ v₀ ξ₀⟫_ℂ).re
  · obtain ⟨v₀, hv₀, ξ₀, hpos⟩ := h0
    set κ₀ : ℝ := (⟪ξ₀, beOp D X v₀ v₀ ξ₀⟫_ℂ).re with hκ₀
    set c : ℂ := (((Real.sqrt κ₀)⁻¹ : ℝ) : ℂ) with hc
    refine ⟨fun u => c • beOp D X u v₀ ξ₀, ⟨?_, ?_, ?_⟩, ?_⟩
    · intro u hu v hv
      have : beOp D X (u + v) v₀ = beOp D X u v₀ + beOp D X v v₀ := by
        unfold beOp
        simp_rw [beInt_add_left]
        exact integral_add (hInt u hu v₀ hv₀) (hInt v hv v₀ hv₀)
      simp only [this, _root_.add_apply, smul_add]
    · intro a u hu
      have : beOp D X (a • u) v₀ = a • beOp D X u v₀ := by
        unfold beOp
        simp_rw [beInt_smul_left]
        exact integral_smul a _
      simp only [this, _root_.smul_apply]
      rw [smul_comm]
    · intro h hh m hm u hu
      simp only [hEq u hu v₀ hv₀ h hh m hm, _root_.smul_apply,
        ContinuousLinearMap.comp_apply, map_smul]
      rw [smul_comm]
    · intro u hu u' hu'
      ext η'
      apply ext_inner_left ℂ
      intro η
      simp only [rk1, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_right,
        inner_smul_left]
      rw [← hH v₀ hv₀ u' hu' η' ξ₀]
      have hmin := hM u hu u' hu' v₀ hv₀ v₀ hv₀ η η' ξ₀ ξ₀
      rw [hre v₀ hv₀ ξ₀] at hmin
      have hcc : starRingEnd ℂ c * c = ((κ₀⁻¹ : ℝ) : ℂ) := by
        rw [hc, Complex.conj_ofReal, ← Complex.ofReal_mul]
        congr 1
        rw [← mul_inv, Real.mul_self_sqrt hpos.le]
      have hk : ((κ₀ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
      calc ⟪η, beOp D X u u' η'⟫_ℂ
          = (starRingEnd ℂ c * c) * (⟪η, beOp D X u u' η'⟫_ℂ * (κ₀ : ℂ)) := by
            rw [hcc, Complex.ofReal_inv]; field_simp
        _ = _ := by rw [hmin]; ring
  · push Not at h0
    have hz : ∀ u ∈ Vfl X, ∀ ξ : Wp, ⟪ξ, beOp D X u u ξ⟫_ℂ = 0 := by
      intro u hu ξ
      rw [hre u hu ξ]
      have := le_antisymm (h0 u hu ξ) (hP u hu ξ)
      simp [this]
    refine ⟨fun _ => 0, ⟨fun _ _ _ _ => by simp, fun _ _ _ => by simp, fun _ _ _ _ _ _ => by simp⟩, ?_⟩
    intro u hu u' hu'
    ext η'
    apply ext_inner_left ℂ
    intro η
    have hm := hM u hu u' hu' u' hu' u hu η η' η' η
    rw [hz u hu η, zero_mul] at hm
    have hc : ⟪η', beOp D X u' u η⟫_ℂ = starRingEnd ℂ ⟪η, beOp D X u u' η'⟫_ℂ := by
      rw [hH u' hu' u hu η η', inner_conj_symm]
    rw [hc, Complex.mul_conj] at hm
    have h3 : Complex.normSq ⟪η, beOp D X u u' η'⟫_ℂ = 0 := by exact_mod_cast hm
    rw [Complex.normSq_eq_zero.mp h3]
    simp [rk1]

end ReciprocityTheory.ChartRestriction.DS.Mult1.TopH

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.TopH

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

def Mn (D : RealPlaceData k r Wp Wp) (X : SigData k r) (u₁ u₂ u₃ u₄ : X.Hs) (e₁ e₂ e₃ e₄ : Wp) : ℂ :=
  ⟪e₁, beOp D X u₁ u₂ e₂⟫_ℂ * ⟪e₃, beOp D X u₃ u₄ e₄⟫_ℂ -
    ⟪e₁, beOp D X u₁ u₄ e₄⟫_ℂ * ⟪e₃, beOp D X u₃ u₂ e₂⟫_ℂ

theorem kbound (B : Wp →L[ℂ] Wp) (e f : Wp) : ‖⟪e, B f⟫_ℂ‖ ≤ ‖e‖ * ‖f‖ * ‖B‖ := by
  calc ‖⟪e, B f⟫_ℂ‖ ≤ ‖e‖ * ‖B f‖ := norm_inner_le_norm _ _
    _ ≤ ‖e‖ * (‖B‖ * ‖f‖) := mul_le_mul_of_nonneg_left (B.le_opNorm f) (norm_nonneg _)
    _ = _ := by ring

theorem joint_int (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hGN : GNIntSharp)
    (ha0 : 0 ≤ X.a) {b Cl : ℝ} (hCl0 : 0 ≤ Cl) (hab : AB k r ≤ X.a - b) (Λ : X.Hs → ℂ)
    (hlm : AEStronglyMeasurable (fun y : Mt k r => Λ (X.σ (Matrix.of y) X.w)) D.μG)
    (hCl : ∀ y ∈ GV k r, ‖Λ (X.σ y X.w)‖ ≤ Cl * gN y ^ b) {φ : Mat k r → ℂ} (hφ : IsTestG φ) :
    Integrable (fun z : Mt k r × Mt k r => φ (Matrix.of z.2) *
      ⟪X.σ (Matrix.of z.1) X.w, X.σ (Matrix.of z.2) X.w⟫_ℂ * Λ (X.σ (Matrix.of z.1) X.w))
      (D.μG.prod D.μG) := by
  have sG := (⟨fun K hK => D.haarG.finite_compact K hK⟩ : IsFiniteMeasureOnCompacts D.μG)
  obtain ⟨K, hK, M, hM0, R, hR0, hRK, hM⟩ := test_bound hφ
  have a1 : AEStronglyMeasurable (fun z : Mt k r × Mt k r => φ (Matrix.of z.2)) (D.μG.prod D.μG) :=
    (aesm_G D (test_cont hφ)).comp_snd
  have a2 : AEStronglyMeasurable (fun z : Mt k r × Mt k r =>
      ⟪X.σ (Matrix.of z.1) X.w, X.σ (Matrix.of z.2) X.w⟫_ℂ) (D.μG.prod D.μG) :=
    ((sig_aesm D X X.w).comp_fst).inner ((sig_aesm D X X.w).comp_snd)
  have a3 : AEStronglyMeasurable (fun z : Mt k r × Mt k r => Λ (X.σ (Matrix.of z.1) X.w))
      (D.μG.prod D.μG) := hlm.comp_fst
  have hint : Integrable (fun z : Mt k r × Mt k r =>
      (M * X.Cw * (KH k r ^ 2 * R) ^ X.a * Cl * gN (Matrix.of z.1) ^ (-(X.a - b))) *
        K.indicator (1 : Mat k r → ℝ) (Matrix.of z.2)) (D.μG.prod D.μG) :=
    ((gN_integrable D hGN hab).const_mul (M * X.Cw * (KH k r ^ 2 * R) ^ X.a * Cl)).mul_prod (int_ind D hK)
  refine hint.mono' ((a1.mul a2).mul a3) ?_
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_G D),
    Measure.quasiMeasurePreserving_snd.ae (ae_G D)] with z hz1 hz2
  have hKp : 0 ≤ (KH k r ^ 2 * R) ^ X.a := Real.rpow_nonneg (mul_nonneg (pow_pos KH_pos 2).le hR0) _
  have hCw := C_nonneg X.dec
  by_cases hxK : Matrix.of z.2 ∈ K
  · have hi : K.indicator (1 : Mat k r → ℝ) (Matrix.of z.2) = 1 := by simp [Set.indicator, hxK]
    have hφx : ‖φ (Matrix.of z.2)‖ ≤ M := by simpa [hi] using hM _ hz2
    have hO' : ‖⟪X.σ (Matrix.of z.1) X.w, X.σ (Matrix.of z.2) X.w⟫_ℂ‖ ≤
        X.Cw * ((KH k r ^ 2 * R) ^ X.a * gN (Matrix.of z.1) ^ (-X.a)) :=
      (orbit_bound X ha0 hz2 hz1).trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (mul_nonneg (pow_pos KH_pos 2).le (gN_nonneg _))
          (mul_le_mul_of_nonneg_left (hRK _ hxK) (pow_pos KH_pos 2).le) ha0)
        (Real.rpow_nonneg (gN_nonneg _) _)) hCw)
    have hl := hCl _ hz1
    have e : gN (Matrix.of z.1) ^ (-(X.a - b)) =
        gN (Matrix.of z.1) ^ (-X.a) * gN (Matrix.of z.1) ^ b := by
      rw [← Real.rpow_add (gN_pos hz1)]; ring_nf
    rw [norm_mul, norm_mul, hi, mul_one, e]
    calc ‖φ (Matrix.of z.2)‖ * ‖⟪X.σ (Matrix.of z.1) X.w, X.σ (Matrix.of z.2) X.w⟫_ℂ‖ *
          ‖Λ (X.σ (Matrix.of z.1) X.w)‖
        ≤ M * (X.Cw * ((KH k r ^ 2 * R) ^ X.a * gN (Matrix.of z.1) ^ (-X.a))) *
          (Cl * gN (Matrix.of z.1) ^ b) :=
          mul_le_mul (mul_le_mul hφx hO' (norm_nonneg _) hM0) hl (norm_nonneg _)
            (mul_nonneg hM0 (mul_nonneg hCw (mul_nonneg hKp (Real.rpow_nonneg (gN_nonneg _) _))))
      _ = _ := by ring
  · have hi : K.indicator (1 : Mat k r → ℝ) (Matrix.of z.2) = 0 := by simp [Set.indicator, hxK]
    have hφx : φ (Matrix.of z.2) = 0 := by
      have := hM _ hz2; rw [hi, mul_zero] at this; exact norm_le_zero_iff.1 this
    rw [hφx, hi]
    simp

theorem step_ii (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hGN : GNIntSharp)
    (ha0 : 0 ≤ X.a) {d b Cl : ℝ} (hd : 0 < d) (hCl0 : 0 ≤ Cl) (hab : AB k r ≤ X.a - b) (Λ : X.Hs → ℂ)
    (hlm : AEStronglyMeasurable (fun y : Mt k r => Λ (X.σ (Matrix.of y) X.w)) D.μG)
    (hCl : ∀ y ∈ GV k r, ‖Λ (X.σ y X.w)‖ ≤ Cl * gN y ^ b)
    (hR : ∀ u ∈ Vfl X, Λ u = (d : ℂ) *
      ∫ y : Mt k r, ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ * Λ (X.σ (Matrix.of y) X.w) ∂D.μG)
    {φ : Mat k r → ℂ} (hφ : IsTestG φ) :
    ∫ x : Mt k r, φ (Matrix.of x) * Λ (X.σ (Matrix.of x) X.w) ∂D.μG = Λ (sigInt D X φ X.w) := by
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have sG := (⟨fun K hK => D.haarG.finite_compact K hK⟩ : IsFiniteMeasureOnCompacts D.μG)
  have hint := sigInt_integrable D X hφ
  have hc : ∀ y : Mt k r, ⟪X.σ (Matrix.of y) X.w, sigInt D X φ X.w⟫_ℂ =
      ∫ x : Mt k r, φ (Matrix.of x) * ⟪X.σ (Matrix.of y) X.w, X.σ (Matrix.of x) X.w⟫_ℂ ∂D.μG := by
    intro y
    unfold sigInt
    rw [← integral_inner hint]
    simp only [inner_smul_right]
  have hFi := joint_int D X hGN ha0 hCl0 hab Λ hlm hCl hφ
  have e1 : Λ (sigInt D X φ X.w) = (d : ℂ) * ∫ y : Mt k r, (∫ x : Mt k r, φ (Matrix.of x) *
      ⟪X.σ (Matrix.of y) X.w, X.σ (Matrix.of x) X.w⟫_ℂ ∂D.μG) * Λ (X.σ (Matrix.of y) X.w) ∂D.μG := by
    rw [hR _ (dd_mem D X ha0 hφ)]
    simp only [hc]
  have e2 : ∀ y : Mt k r, (∫ x : Mt k r, φ (Matrix.of x) *
        ⟪X.σ (Matrix.of y) X.w, X.σ (Matrix.of x) X.w⟫_ℂ ∂D.μG) * Λ (X.σ (Matrix.of y) X.w) =
      ∫ x : Mt k r, φ (Matrix.of x) * ⟪X.σ (Matrix.of y) X.w, X.σ (Matrix.of x) X.w⟫_ℂ *
        Λ (X.σ (Matrix.of y) X.w) ∂D.μG := fun y => (integral_mul_const _ _).symm
  have e3 := integral_integral_swap (μ := D.μG) (ν := D.μG) (f := fun y x : Mt k r => φ (Matrix.of x) *
      ⟪X.σ (Matrix.of y) X.w, X.σ (Matrix.of x) X.w⟫_ℂ * Λ (X.σ (Matrix.of y) X.w)) hFi
  have e4 : ∀ᵐ x ∂D.μG, ∫ y : Mt k r, φ (Matrix.of x) * ⟪X.σ (Matrix.of y) X.w, X.σ (Matrix.of x) X.w⟫_ℂ *
        Λ (X.σ (Matrix.of y) X.w) ∂D.μG = φ (Matrix.of x) * Λ (X.σ (Matrix.of x) X.w) / d := by
    filter_upwards [ae_G D] with x hx
    have hx' := hR _ (sig_mem_vfl X ha0 hx (w_mem X))
    have e5 : ∀ y : Mt k r, φ (Matrix.of x) * ⟪X.σ (Matrix.of y) X.w, X.σ (Matrix.of x) X.w⟫_ℂ *
        Λ (X.σ (Matrix.of y) X.w) = φ (Matrix.of x) * (⟪X.σ (Matrix.of y) X.w, X.σ (Matrix.of x) X.w⟫_ℂ *
        Λ (X.σ (Matrix.of y) X.w)) := fun y => mul_assoc _ _ _
    simp only [e5]
    rw [integral_const_mul, hx']
    field_simp
  rw [e1]
  simp only [e2]
  rw [e3, integral_congr_ae e4, integral_div]
  field_simp

theorem vanish_core (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hGN : GNIntSharp)
    (ha0 : 0 ≤ X.a) {d b : ℝ} (hd : 0 < d) (hb0 : 0 ≤ b) (hab : AB k r ≤ X.a - b)
    (Λ : X.Hs → ℂ)
    (hlm : AEStronglyMeasurable (fun y : Mt k r => Λ (X.σ (Matrix.of y) X.w)) D.μG)
    (hlb : ∃ C : ℝ, ∀ y ∈ GV k r, ‖Λ (X.σ y X.w)‖ ≤ C * gN y ^ b)
    (hR : ∀ u ∈ Vfl X, Λ u = (d : ℂ) *
      ∫ y : Mt k r, ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ * Λ (X.σ (Matrix.of y) X.w) ∂D.μG)
    (h0 : ∀ φ : Mat k r → ℂ, IsTestG φ → Λ (sigInt D X φ X.w) = 0) :
    ∀ u ∈ Vfl X, Λ u = 0 := by
  obtain ⟨Cl, hCl⟩ := hlb
  have hCl0 : 0 ≤ Cl := C_nonneg hCl
  have sG := (⟨fun K hK => D.haarG.finite_compact K hK⟩ : IsFiniteMeasureOnCompacts D.μG)
  have hli : LocallyIntegrable (fun y : Mt k r => Λ (X.σ (Matrix.of y) X.w)) D.μG := by
    refine (locallyIntegrable_iff).2 fun K hK => ?_
    obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn gN_cont.continuousOn
    have hfin : IsFiniteMeasure (D.μG.restrict K) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact D.haarG.finite_compact K hK⟩
    refine Integrable.mono' (integrable_const (Cl * (max R 0) ^ b)) hlm.restrict ?_
    filter_upwards [ae_restrict_mem hK.measurableSet, ae_restrict_of_ae (ae_G D)] with y hyK hyG
    refine (hCl _ hyG).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (gN_nonneg _) ?_ hb0) hCl0)
    exact ((Real.le_norm_self _).trans (hR y hyK)).trans (le_max_left _ _)
  have hae : ∀ᵐ y ∂D.μG, Λ (X.σ (Matrix.of y) X.w) = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hli fun g hg hgc => ?_
    have h1 := step_ii D X hGN ha0 hd hCl0 hab Λ hlm hCl hR (test_of_contDiff hg hgc)
    rw [h0 _ (test_of_contDiff hg hgc)] at h1
    rw [← h1]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => Complex.real_smul)
  intro u hu
  rw [hR u hu]
  have : ∫ y : Mt k r, ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ * Λ (X.σ (Matrix.of y) X.w) ∂D.μG = 0 :=
    integral_eq_zero_of_ae (by filter_upwards [hae] with y hy; simp [hy])
  rw [this, mul_zero]

end ReciprocityTheory.ChartRestriction.DS.Mult1.TopH
end
end
end

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.TopH

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

theorem repro_scalar (D : RealPlaceData k r Wp Wp) (X : SigData k r) (d : ℝ) {u v : X.Hs} (e f : Wp)
    (hI : Integrable (fun y : Mt k r => ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ •
      beOp D X (X.σ (Matrix.of y) X.w) v) D.μG)
    (hR : beOp D X u v = (d : ℂ) • ∫ y : Mt k r, ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ •
      beOp D X (X.σ (Matrix.of y) X.w) v ∂D.μG) :
    Integrable (fun y : Mt k r => ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ *
      ⟪e, beOp D X (X.σ (Matrix.of y) X.w) v f⟫_ℂ) D.μG ∧
    ⟪e, beOp D X u v f⟫_ℂ = (d : ℂ) * ∫ y : Mt k r, ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ *
      ⟪e, beOp D X (X.σ (Matrix.of y) X.w) v f⟫_ℂ ∂D.μG := by
  let L : (Wp →L[ℂ] Wp) →L[ℂ] ℂ := (innerSL ℂ e).comp (ContinuousLinearMap.apply ℂ Wp f)
  have hL : ∀ A : Wp →L[ℂ] Wp, L A = ⟪e, A f⟫_ℂ := fun A => by
    simp [L, innerSL_apply_apply]
  have hLa : ∀ (c : ℂ) (A : Wp →L[ℂ] Wp), L (c • A) = c * ⟪e, A f⟫_ℂ := fun c A => by
    rw [map_smul, hL, smul_eq_mul]
  refine ⟨(L.integrable_comp hI).congr (Filter.Eventually.of_forall fun y => hLa _ _), ?_⟩
  rw [hR, ContinuousLinearMap.smul_apply, inner_smul_right, ← hL, ← L.integral_comp_comm hI]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => hLa _ _)

theorem opint (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hGN : GNIntSharp) (ha0 : 0 ≤ X.a) {b : ℝ}
    (hab : AB k r ≤ X.a - b) {u v : X.Hs} (hu : u ∈ Vfl X)
    (hbv : ∃ C : ℝ, ∀ y ∈ GV k r, ‖beOp D X (X.σ y X.w) v‖ ≤ C * gN y ^ b) :
    Integrable (fun y : Mt k r => ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ •
      beOp D X (X.σ (Matrix.of y) X.w) v) D.μG := by
  obtain ⟨Cc, hCc0, hCc⟩ := coef_bound X ha0 hu
  obtain ⟨Cb, hCb⟩ := hbv
  have hm : AEStronglyMeasurable (fun y : Mt k r => ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ •
      beOp D X (X.σ (Matrix.of y) X.w) v) D.μG :=
    (show AEStronglyMeasurable (fun y : Mt k r => ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ) D.μG from
      (sig_aesm D X X.w).inner aestronglyMeasurable_const).smul (be_aesm D X v)
  refine ((gN_integrable D hGN hab).const_mul (Cc * Cb)).mono' hm ?_
  filter_upwards [ae_G D] with y hy
  rw [norm_smul]
  have e : gN (Matrix.of y) ^ (-(X.a - b)) = gN (Matrix.of y) ^ (-X.a) * gN (Matrix.of y) ^ b := by
    rw [← Real.rpow_add (gN_pos hy)]; ring_nf
  rw [e]
  calc ‖⟪X.σ (Matrix.of y) X.w, u⟫_ℂ‖ * ‖beOp D X (X.σ (Matrix.of y) X.w) v‖
      ≤ (Cc * gN (Matrix.of y) ^ (-X.a)) * (Cb * gN (Matrix.of y) ^ b) :=
        mul_le_mul (hCc _ hy) (hCb _ hy) (norm_nonneg _)
          (mul_nonneg hCc0 (Real.rpow_nonneg (gN_nonneg _) _))
    _ = _ := by ring

theorem ext1 (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hGN : GNIntSharp) (ha0 : 0 ≤ X.a) {d b : ℝ}
    (hd : 0 < d) (hb0 : 0 ≤ b) (hab : AB k r ≤ X.a - b)
    (hbe : ∀ v ∈ Vfl X, ∃ C : ℝ, ∀ y ∈ GV k r, ‖beOp D X (X.σ y X.w) v‖ ≤ C * gN y ^ b)
    (hRep : ∀ u ∈ Vfl X, ∀ v ∈ Vfl X, beOp D X u v = (d : ℂ) • ∫ y : Mt k r,
      ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ • beOp D X (X.σ (Matrix.of y) X.w) v ∂D.μG)
    {u₂ u₄ : X.Hs} (hu₂ : u₂ ∈ Vfl X) (hu₄ : u₄ ∈ Vfl X) (u₃ : X.Hs) (e₁ e₂ e₃ e₄ : Wp)
    (h : ∀ φ : Mat k r → ℂ, IsTestG φ → Mn D X (sigInt D X φ X.w) u₂ u₃ u₄ e₁ e₂ e₃ e₄ = 0) :
    ∀ u ∈ Vfl X, Mn D X u u₂ u₃ u₄ e₁ e₂ e₃ e₄ = 0 := by
  refine vanish_core D X hGN ha0 hd hb0 hab (fun u => Mn D X u u₂ u₃ u₄ e₁ e₂ e₃ e₄) ?_ ?_ ?_ h
  · let L₂ : (Wp →L[ℂ] Wp) →L[ℂ] ℂ := (innerSL ℂ e₁).comp (ContinuousLinearMap.apply ℂ Wp e₂)
    let L₄ : (Wp →L[ℂ] Wp) →L[ℂ] ℂ := (innerSL ℂ e₁).comp (ContinuousLinearMap.apply ℂ Wp e₄)
    have m2 := L₂.continuous.comp_aestronglyMeasurable (be_aesm D X u₂)
    have m4 := L₄.continuous.comp_aestronglyMeasurable (be_aesm D X u₄)
    exact (m2.mul aestronglyMeasurable_const).sub (m4.mul aestronglyMeasurable_const)
  · obtain ⟨C₂, h₂⟩ := hbe u₂ hu₂
    obtain ⟨C₄, h₄⟩ := hbe u₄ hu₄
    refine ⟨‖e₁‖ * ‖e₂‖ * C₂ * ‖⟪e₃, beOp D X u₃ u₄ e₄⟫_ℂ‖ +
      ‖e₁‖ * ‖e₄‖ * C₄ * ‖⟪e₃, beOp D X u₃ u₂ e₂⟫_ℂ‖, fun y hy => ?_⟩
    simp only [Mn]
    calc ‖⟪e₁, beOp D X (X.σ y X.w) u₂ e₂⟫_ℂ * ⟪e₃, beOp D X u₃ u₄ e₄⟫_ℂ -
          ⟪e₁, beOp D X (X.σ y X.w) u₄ e₄⟫_ℂ * ⟪e₃, beOp D X u₃ u₂ e₂⟫_ℂ‖
        ≤ ‖⟪e₁, beOp D X (X.σ y X.w) u₂ e₂⟫_ℂ‖ * ‖⟪e₃, beOp D X u₃ u₄ e₄⟫_ℂ‖ +
          ‖⟪e₁, beOp D X (X.σ y X.w) u₄ e₄⟫_ℂ‖ * ‖⟪e₃, beOp D X u₃ u₂ e₂⟫_ℂ‖ := by
          rw [← norm_mul, ← norm_mul]; exact norm_sub_le _ _
      _ ≤ (‖e₁‖ * ‖e₂‖ * (C₂ * gN y ^ b)) * ‖⟪e₃, beOp D X u₃ u₄ e₄⟫_ℂ‖ +
          (‖e₁‖ * ‖e₄‖ * (C₄ * gN y ^ b)) * ‖⟪e₃, beOp D X u₃ u₂ e₂⟫_ℂ‖ :=
          add_le_add
            (mul_le_mul_of_nonneg_right ((kbound _ _ _).trans
              (mul_le_mul_of_nonneg_left (h₂ y hy) (by positivity))) (norm_nonneg _))
            (mul_le_mul_of_nonneg_right ((kbound _ _ _).trans
              (mul_le_mul_of_nonneg_left (h₄ y hy) (by positivity))) (norm_nonneg _))
      _ = _ := by ring
  · intro u hu
    obtain ⟨i2, r2⟩ := repro_scalar D X d e₁ e₂ (opint D X hGN ha0 hab hu (hbe u₂ hu₂)) (hRep u hu u₂ hu₂)
    obtain ⟨i4, r4⟩ := repro_scalar D X d e₁ e₄ (opint D X hGN ha0 hab hu (hbe u₄ hu₄)) (hRep u hu u₄ hu₄)
    have e5 : ∀ y : Mt k r, ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ *
        Mn D X (X.σ (Matrix.of y) X.w) u₂ u₃ u₄ e₁ e₂ e₃ e₄ =
        (⟪X.σ (Matrix.of y) X.w, u⟫_ℂ * ⟪e₁, beOp D X (X.σ (Matrix.of y) X.w) u₂ e₂⟫_ℂ) *
          ⟪e₃, beOp D X u₃ u₄ e₄⟫_ℂ -
        (⟪X.σ (Matrix.of y) X.w, u⟫_ℂ * ⟪e₁, beOp D X (X.σ (Matrix.of y) X.w) u₄ e₄⟫_ℂ) *
          ⟪e₃, beOp D X u₃ u₂ e₂⟫_ℂ := fun y => by simp only [Mn]; ring
    show Mn D X u u₂ u₃ u₄ e₁ e₂ e₃ e₄ = (d : ℂ) * ∫ y : Mt k r, ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ *
      Mn D X (X.σ (Matrix.of y) X.w) u₂ u₃ u₄ e₁ e₂ e₃ e₄ ∂D.μG
    simp only [e5]
    rw [integral_sub (i2.mul_const _) (i4.mul_const _), integral_mul_const, integral_mul_const]
    simp only [Mn]
    rw [r2, r4]
    ring

theorem mn_swap (D : RealPlaceData k r Wp Wp) (X : SigData k r) (u₁ u₂ u₃ u₄ : X.Hs) (e₁ e₂ e₃ e₄ : Wp) :
    Mn D X u₃ u₂ u₁ u₄ e₃ e₂ e₁ e₄ = -Mn D X u₁ u₂ u₃ u₄ e₁ e₂ e₃ e₄ := by
  unfold Mn; ring

theorem mn_herm (D : RealPlaceData k r Wp Wp) (X : SigData k r)
    (hH : ∀ u ∈ Vfl X, ∀ u' ∈ Vfl X, ∀ η ξ : Wp, ⟪ξ, beOp D X u u' η⟫_ℂ = ⟪beOp D X u' u ξ, η⟫_ℂ)
    {u₁ u₂ u₃ u₄ : X.Hs} (h₁ : u₁ ∈ Vfl X) (h₂ : u₂ ∈ Vfl X) (h₃ : u₃ ∈ Vfl X) (h₄ : u₄ ∈ Vfl X)
    (e₁ e₂ e₃ e₄ : Wp) :
    Mn D X u₂ u₁ u₄ u₃ e₂ e₁ e₄ e₃ = starRingEnd ℂ (Mn D X u₁ u₂ u₃ u₄ e₁ e₂ e₃ e₄) := by
  have kc : ∀ u ∈ Vfl X, ∀ v ∈ Vfl X, ∀ e f : Wp,
      ⟪f, beOp D X v u e⟫_ℂ = starRingEnd ℂ ⟪e, beOp D X u v f⟫_ℂ := by
    intro u hu v hv e f
    rw [hH v hv u hu e f, inner_conj_symm]
  unfold Mn
  rw [kc u₁ h₁ u₂ h₂ e₁ e₂, kc u₃ h₃ u₄ h₄ e₃ e₄, kc u₃ h₃ u₂ h₂ e₃ e₂, kc u₁ h₁ u₄ h₄ e₁ e₄]
  simp only [map_sub, map_mul]
  ring

theorem minorsOn_of_DD (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hGN : GNIntSharp) (ha0 : 0 ≤ X.a)
    {d b : ℝ} (hd : 0 < d) (hb0 : 0 ≤ b) (hab : AB k r ≤ X.a - b)
    (hbe : ∀ v ∈ Vfl X, ∃ C : ℝ, ∀ y ∈ GV k r, ‖beOp D X (X.σ y X.w) v‖ ≤ C * gN y ^ b)
    (hRep : ∀ u ∈ Vfl X, ∀ v ∈ Vfl X, beOp D X u v = (d : ℂ) • ∫ y : Mt k r,
      ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ • beOp D X (X.σ (Matrix.of y) X.w) v ∂D.μG)
    (hH : ∀ u ∈ Vfl X, ∀ u' ∈ Vfl X, ∀ η ξ : Wp, ⟪ξ, beOp D X u u' η⟫_ℂ = ⟪beOp D X u' u ξ, η⟫_ℂ)
    (hDD : ∀ u₁ ∈ DDinf D X, ∀ u₂ ∈ DDinf D X, ∀ u₃ ∈ DDinf D X, ∀ u₄ ∈ DDinf D X, ∀ e₁ e₂ e₃ e₄ : Wp,
      Mn D X u₁ u₂ u₃ u₄ e₁ e₂ e₃ e₄ = 0) : MinorsOn D X := by
  have hDV : ∀ u ∈ DDinf D X, u ∈ Vfl X := by
    rintro u ⟨φ, hφ, rfl⟩; exact dd_mem D X ha0 hφ
  have hT : ∀ φ : Mat k r → ℂ, IsTestG φ → sigInt D X φ X.w ∈ DDinf D X := fun φ hφ => ⟨φ, hφ, rfl⟩
  have S1 : ∀ u₁ ∈ Vfl X, ∀ u₂ ∈ DDinf D X, ∀ u₃ ∈ DDinf D X, ∀ u₄ ∈ DDinf D X, ∀ e₁ e₂ e₃ e₄ : Wp,
      Mn D X u₁ u₂ u₃ u₄ e₁ e₂ e₃ e₄ = 0 := by
    intro u₁ hu₁ u₂ hu₂ u₃ hu₃ u₄ hu₄ e₁ e₂ e₃ e₄
    exact ext1 D X hGN ha0 hd hb0 hab hbe hRep (hDV _ hu₂) (hDV _ hu₄) u₃ e₁ e₂ e₃ e₄
      (fun φ hφ => hDD _ (hT φ hφ) _ hu₂ _ hu₃ _ hu₄ e₁ e₂ e₃ e₄) u₁ hu₁
  have S2 : ∀ u₁ ∈ Vfl X, ∀ u₂ ∈ DDinf D X, ∀ u₃ ∈ Vfl X, ∀ u₄ ∈ DDinf D X, ∀ e₁ e₂ e₃ e₄ : Wp,
      Mn D X u₁ u₂ u₃ u₄ e₁ e₂ e₃ e₄ = 0 := by
    intro u₁ hu₁ u₂ hu₂ u₃ hu₃ u₄ hu₄ e₁ e₂ e₃ e₄
    rw [← neg_eq_zero, ← mn_swap]
    exact ext1 D X hGN ha0 hd hb0 hab hbe hRep (hDV _ hu₂) (hDV _ hu₄) u₁ e₃ e₂ e₁ e₄
      (fun φ hφ => by
        rw [← neg_eq_zero, ← mn_swap]
        exact S1 u₁ hu₁ _ hu₂ _ (hT φ hφ) _ hu₄ e₁ e₂ e₃ e₄) u₃ hu₃
  have S3 : ∀ u₁ ∈ DDinf D X, ∀ u₂ ∈ Vfl X, ∀ u₃ ∈ DDinf D X, ∀ u₄ ∈ Vfl X, ∀ e₁ e₂ e₃ e₄ : Wp,
      Mn D X u₁ u₂ u₃ u₄ e₁ e₂ e₃ e₄ = 0 := by
    intro u₁ hu₁ u₂ hu₂ u₃ hu₃ u₄ hu₄ e₁ e₂ e₃ e₄
    rw [mn_herm D X hH hu₂ (hDV _ hu₁) hu₄ (hDV _ hu₃) e₂ e₁ e₄ e₃,
      S2 u₂ hu₂ u₁ hu₁ u₄ hu₄ u₃ hu₃ e₂ e₁ e₄ e₃, map_zero]
  have S4 : ∀ u₁ ∈ Vfl X, ∀ u₂ ∈ Vfl X, ∀ u₃ ∈ DDinf D X, ∀ u₄ ∈ Vfl X, ∀ e₁ e₂ e₃ e₄ : Wp,
      Mn D X u₁ u₂ u₃ u₄ e₁ e₂ e₃ e₄ = 0 := by
    intro u₁ hu₁ u₂ hu₂ u₃ hu₃ u₄ hu₄ e₁ e₂ e₃ e₄
    exact ext1 D X hGN ha0 hd hb0 hab hbe hRep hu₂ hu₄ u₃ e₁ e₂ e₃ e₄
      (fun φ hφ => S3 _ (hT φ hφ) _ hu₂ _ hu₃ _ hu₄ e₁ e₂ e₃ e₄) u₁ hu₁
  intro u₁ hu₁ u₂ hu₂ u₃ hu₃ u₄ hu₄ e₁ e₂ e₃ e₄
  have : Mn D X u₁ u₂ u₃ u₄ e₁ e₂ e₃ e₄ = 0 := by
    rw [← neg_eq_zero, ← mn_swap]
    exact ext1 D X hGN ha0 hd hb0 hab hbe hRep hu₂ hu₄ u₁ e₃ e₂ e₁ e₄
      (fun φ hφ => by
        rw [← neg_eq_zero, ← mn_swap]
        exact S4 u₁ hu₁ u₂ hu₂ _ (hT φ hφ) u₄ hu₄ e₁ e₂ e₃ e₄) u₃ hu₃
  exact sub_eq_zero.1 this

end ReciprocityTheory.ChartRestriction.DS.Mult1.TopH
end
end

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.TopH

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

theorem isHaarOn_smul {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) {c : ℝ≥0} (hc : 0 < c) :
    IsHaarOn U ((c : ℝ≥0∞) • μ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [h.conc]
  · intro a ha
    have hcont : Continuous (lmulM a : Mt k r → Mt k r) :=
      continuous_const.matrix_mul continuous_id
    rw [Measure.map_smul (c : ℝ≥0∞) hcont.measurable.aemeasurable, h.left a ha]
  · intro a ha
    have hcont : Continuous (rmulF a : Mt k r → Mt k r) :=
      continuous_id.matrix_mul continuous_const
    rw [Measure.map_smul (c : ℝ≥0∞) hcont.measurable.aemeasurable, h.right a ha]
  · intro K hK
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top (h.finite_compact K hK)
  · intro h0
    have h1 : (c : ℝ≥0∞) * μ Set.univ = 0 := by
      rw [← smul_eq_mul, ← smul_apply, h0]; rfl
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact absurd h2 (by exact_mod_cast hc.ne')
    · exact h.ne_zero (Measure.measure_univ_eq_zero.1 h2)

def rescale (D : RealPlaceData k r Wp Wp) {c : ℝ≥0} (hc : 0 < c) : RealPlaceData k r Wp Wp :=
  { D with μG := (c : ℝ≥0∞) • D.μG, haarG := isHaarOn_smul D.haarG hc }

theorem ccInt_of (D : RealPlaceData k r Wp Wp) (hGN : GNIntSharp) {A : ℝ} (hA : AB k r ≤ A) {c : ℝ≥0} (hc : 0 < c) :
    CCIntegrable (rescale D hc) A := by
  intro F c' _ hF
  show (∫⁻ g : Mt k r, ‖F (Matrix.of g)‖ₑ ∂((c : ℝ≥0∞) • D.μG)) < ∞
  rw [lintegral_smul_measure]
  refine ENNReal.mul_lt_top ENNReal.coe_lt_top ?_
  have hfin := hGN k r D.μG A D.haarG hA
  have hb : ∀ᵐ g ∂D.μG, ‖F (Matrix.of g)‖ₑ ≤
      ENNReal.ofReal (max c' 0) * ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) := by
    filter_upwards [ae_G D] with g hg
    have hp : 0 < gN (Matrix.of g) ^ A := Real.rpow_pos_of_pos (gN_pos hg) A
    have h1 : ‖F (Matrix.of g)‖ ≤ max c' 0 * gN (Matrix.of g) ^ (-A) := by
      rw [Real.rpow_neg (gN_nonneg _), ← div_eq_mul_inv, le_div_iff₀ hp, mul_comm]
      exact (hF _ hg).trans (le_max_left _ _)
    rw [← ENNReal.ofReal_mul (le_max_right _ _), ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal h1
  refine lt_of_le_of_lt (lintegral_mono_ae hb) ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

theorem jcont_of (hIn : UnitaryGroupStructuralFacts) (D : RealPlaceData k r Wp Wp) {A : ℝ} (hA : AB k r ≤ A) : JCont D A := by
  obtain ⟨hB2, -, -, -, -, -, -, hJC, -, -, -, -, -, -, hINB, -⟩ := hIn
  obtain ⟨c, ⟨hc, hIF⟩, -⟩ := hINB k r Wp Wp D
  have hGN : GNIntSharp := hB2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact hJC k r Wp Wp (rescale D hc) A hIF (ccInt_of D hGN hA hc)

theorem lemB_of (hIn : UnitaryGroupStructuralFacts) (hXi : XiExists) (D : RealPlaceData k r Wp Wp) {A : ℝ} (hA : AB k r ≤ A) :
    ∃ c : ℝ, 0 < c ∧ ∀ F F' : Mat k r → (Wp →L[ℂ] Wp), InCC A 5 F → InCC A 5 F' →
      beta D F F' = (c : ℂ) * betaInf D F F' := by
  obtain ⟨-, -, -, -, -, -, hLBX, -⟩ := hIn
  obtain ⟨c, hc, -, -, hB, -⟩ := (hLBX hXi).2 k r Wp Wp D A hA
  exact ⟨c, by exact_mod_cast hc, hB⟩

theorem hs_ext {A B : Wp →L[ℂ] Wp} (h : ∀ X₀ : Wp →L[ℂ] Wp, hsInner A X₀ = hsInner B X₀) : A = B := by
  have hlin : hsVec (A - B) = hsVec A - hsVec B := by
    ext i; simp [hsVec]
  have h1 : inner ℂ (hsVec (A - B)) (hsVec (A - B)) = 0 := by
    have := h (A - B)
    unfold hsInner at this
    rw [hlin] at this ⊢
    rw [inner_sub_right, this, sub_self]
  rw [inner_self_eq_zero] at h1
  rw [← sub_eq_zero]
  apply ContinuousLinearMap.coe_injective
  refine (stdOrthonormalBasis ℂ Wp).toBasis.ext fun i => ?_
  have := congrArg (fun v => v i) h1
  simpa [hsVec] using this

end ReciprocityTheory.ChartRestriction.DS.Mult1.TopH

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.TopH

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

theorem nR_ge (hk : 1 ≤ k) : (2 : ℝ) ≤ nR k r := by
  unfold nR
  have : 2 ≤ 2 * r + k + 1 := by omega
  exact_mod_cast this

theorem half_ratio_le_segment_base_of_std (hk : 1 ≤ k) {a : ℝ} (ha : aM k r ≤ a) : AB k r ≤ a - AG k r - 1 := by
  have hn := nR_ge (r := r) hk
  have e : nR k r = 2 * (r : ℝ) + k + 1 := by unfold nR; push_cast; ring
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : 2 * ((k : ℝ) + r) * ((r : ℝ) + 1) + 1 ≤ nR k r ^ 2 := by rw [e]; nlinarith
  have h2 : 2 * nR k r ^ 2 + 1 ≤ 4 * nR k r ^ 3 := by nlinarith
  unfold AB AG; unfold aM at ha
  linarith

theorem decay_exponent_ge_double_shift (hk : 1 ≤ k) {a : ℝ} (ha : aM k r ≤ a) : AS k r + 1 ≤ a - AG k r - 1 - AG k r - 1 := by
  have hn := nR_ge (r := r) hk
  have h2 : nR k r ^ 3 + 2 * nR k r ^ 2 + 3 ≤ 4 * nR k r ^ 3 := by nlinarith
  unfold AS AG; unfold aM at ha
  linarith

theorem beInt_int_mixed (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hD : IsDiag D) (hX : SqIntG D X)
    (ha : aM k r ≤ X.a) (h0 : StSchurG) (h1 : StPairs) (h1' : StBeConv) {u v : X.Hs}
    (hu : u ∈ VflA X (X.a - AG k r - 1)) (hv : v ∈ Vfl X) : Integrable (beInt D X u v) (D.μW.prod D.μN) := by
  obtain ⟨d, hd⟩ := h0 k r Wp D X hD hX
  obtain ⟨C, hC⟩ := h1 k r Wp D X hD hX d hd (X.a - AG k r - 1) X.a u hu v hv
  have hAG : 0 ≤ AG k r := by unfold AG; positivity
  have hmin : min (X.a - AG k r - 1) X.a = X.a - AG k r - 1 := min_eq_left (by linarith)
  rw [hmin] at hC
  exact h1' k r Wp D X hD hX _ (decay_exponent_ge_double_shift D.k_pos ha) u v ⟨C, hC⟩

theorem psiD_one (D : RealPlaceData k r Wp Wp) : psiD D 1 = 1 := by
  have h : ∀ a : Fin r, (if h : a.val + 1 < r then (1 : Mat k r) (eI k r a) (eI k r ⟨a.val + 1, h⟩)
      else ((1 : Mat k r) *ᵥ D.z) (eI k r a)) = 0 := by
    intro a
    split_ifs with h
    · rw [Matrix.one_apply_ne]
      intro he
      have := congrArg Fin.val he
      simp [eI] at this
    · rw [Matrix.one_mulVec]
      exact D.z_mem _ (Or.inl a.isLt)
  unfold psiD psi ell
  rw [Finset.sum_eq_zero (fun a _ => h a)]
  simp

theorem pi_adj (D : RealPlaceData k r Wp Wp) {g : Mat k r} (hg : g ∈ UWset k r D.z) :
    ContinuousLinearMap.adjoint (D.π g) = D.π g⁻¹ := by
  have hgi := uw_inv_mem hg
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  let L : Wp →ₗᵢ[ℂ] Wp := { toLinearMap := (D.π g : Wp →ₗ[ℂ] Wp), norm_map' := D.π_unitary g hg }
  have h1 : D.π g (D.π g⁻¹ x) = x := by
    rw [← ContinuousLinearMap.comp_apply, ← D.π_rep.2 g hg g⁻¹ hgi, gv_mul_inv (uw_gv hg), D.π_rep.1]
    rfl
  calc ⟪D.π g⁻¹ x, y⟫_ℂ = ⟪L (D.π g⁻¹ x), L y⟫_ℂ := (L.inner_map_map _ _).symm
    _ = ⟪x, D.π g y⟫_ℂ := by
        show ⟪D.π g (D.π g⁻¹ x), D.π g y⟫_ℂ = _
        rw [h1]

theorem ae_UN' (D : RealPlaceData k r Wp Wp) :
    ∀ᵐ p ∂(D.μW'.prod D.μN), Matrix.of p.1 ∈ UWset k r D.z' ∧ Matrix.of p.2 ∈ Nset k r := by
  have : IsFiniteMeasureOnCompacts D.μW' := ⟨fun K hK => D.haarW'.finite_compact K hK⟩
  have : IsFiniteMeasureOnCompacts D.μN := ⟨fun K hK => D.haarN.finite_compact K hK⟩
  have h1 : ∀ᵐ x ∂D.μW', Matrix.of x ∈ UWset k r D.z' := ae_iff.2 D.haarW'.conc
  have h2 : ∀ᵐ x ∂D.μN, Matrix.of x ∈ Nset k r := ae_iff.2 D.haarN.conc
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae h1, Measure.quasiMeasurePreserving_snd.ae h2]
    with p hp1 hp2
  exact ⟨hp1, hp2⟩

theorem ae_SS (D : RealPlaceData k r Wp Wp) : ∀ᵐ p ∂D.μSS, D.inSS p := by
  have : IsFiniteMeasureOnCompacts D.μW' := ⟨fun K hK => D.haarW'.finite_compact K hK⟩
  have : IsFiniteMeasureOnCompacts D.μW := ⟨fun K hK => D.haarW.finite_compact K hK⟩
  have : IsFiniteMeasureOnCompacts D.μN := ⟨fun K hK => D.haarN.finite_compact K hK⟩
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_UN D),
    Measure.quasiMeasurePreserving_snd.ae (ae_UN' D)] with p h1 h2
  exact ⟨h1.1, h1.2, h2.1, h2.2⟩

theorem incc_dd (hSm : StSmooth) (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hD : IsDiag D) (hX : SqIntG D X)
    (ha : aM k r ≤ X.a) {a b : X.Hs} (ha' : a ∈ DDinf D X) (hb : b ∈ DDinf D X) :
    InCC (X.a - AG k r - 1) 5 (mc X a b) := by
  obtain ⟨φ, hφ, rfl⟩ := ha'
  obtain ⟨φ', hφ', rfl⟩ := hb
  exact hSm k r Wp D X hD hX ha φ φ' hφ hφ' 5

theorem beta_val (h1p : StCut1p) (h2 : StCut2) (hBI : StBetaInf) (hXi : XiExists)
    (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hD : IsDiag D) {d : ℝ} (hd : IsFdegG D X d)
    {A : ℝ} (hA : AB k r ≤ A) {c : ℝ}
    (hcB : ∀ F F' : Mat k r → (Wp →L[ℂ] Wp), InCC A 5 F → InCC A 5 F' → beta D F F' = (c : ℂ) * betaInf D F F')
    (f : Mat k r → ℂ) (x y a₂ b₂ : X.Hs) (X₀ : Wp →L[ℂ] Wp) (hf : ∀ g ∈ GV k r, f g = mc X x y g)
    (hfc : InCC A 5 f) (hc2 : InCC A 5 (mc X a₂ b₂))
    (hxa : Integrable (beInt D X x a₂) (D.μW.prod D.μN)) (hyb : Integrable (beInt D X y b₂) (D.μW.prod D.μN)) :
    beta D (scalF Wp f) (fun g => mc X a₂ b₂ g • X₀) =
      (c : ℂ) * (hsInner ((ContinuousLinearMap.adjoint (beOp D X y b₂)).comp (beOp D X x a₂)) X₀ / (d : ℂ)) := by
  obtain ⟨hI, hval⟩ := h2 k r Wp D X hD d hd f x y a₂ b₂ X₀ hf hxa hyb
  have i1 : InCC A 5 (scalF Wp f) := h1p k r Wp A 5 f (ContinuousLinearMap.id ℂ Wp) hfc
  have i2 : InCC A 5 (fun g => mc X a₂ b₂ g • X₀) := h1p k r Wp A 5 _ X₀ hc2
  rw [hcB _ _ i1 i2, hBI k r Wp Wp D A hXi hA _ _ i1 i2 hI, hval]

theorem beta_zero (h3 : StCut3) (hInv : StInvGroup) (h1p : StCut1p) (hBI : StBetaInf) (hXi : XiExists)
    (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hD : IsDiag D) (hX : SqIntG D X)
    {A : ℝ} (hA : AB k r ≤ A) {c : ℝ}
    (hcB : ∀ F F' : Mat k r → (Wp →L[ℂ] Wp), InCC A 5 F → InCC A 5 F' → beta D F F' = (c : ℂ) * betaInf D F F')
    (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hγ : IsZFrame k r D.z γ)
    (hZ : ∀ x y x' y' : X.Hs,
      ∫ g : Mt k r, ⟪y, X.σ (th k r γ (Matrix.of g)) x⟫_ℂ * star ⟪y', X.σ (Matrix.of g) x'⟫_ℂ ∂D.μG = 0)
    (a₁ b₁ a₂ b₂ : X.Hs) (X₀ : Wp →L[ℂ] Wp) (hf : InCC A 5 (mc X a₁ b₁ ∘ th k r γ))
    (hc2 : InCC A 5 (mc X a₂ b₂)) :
    beta D (scalF Wp (mc X a₁ b₁ ∘ th k r γ)) (fun g => mc X a₂ b₂ g • X₀) = 0 := by
  have hPh : ∀ᵐ p ∂D.μSS, Ph D (scalF Wp (mc X a₁ b₁ ∘ th k r γ)) (fun g => mc X a₂ b₂ g • X₀) p = 0 := by
    filter_upwards [ae_SS D] with p hp
    exact h3 hInv k r Wp D X hD hX γ hγ hZ a₁ b₁ a₂ b₂ X₀ p hp
  have hI : Integrable (Ph D (scalF Wp (mc X a₁ b₁ ∘ th k r γ)) (fun g => mc X a₂ b₂ g • X₀)) D.μSS :=
    (integrable_zero _ _ _).congr (hPh.mono fun p hp => hp.symm)
  have i1 : InCC A 5 (scalF Wp (mc X a₁ b₁ ∘ th k r γ)) := h1p k r Wp A 5 _ (ContinuousLinearMap.id ℂ Wp) hf
  have i2 : InCC A 5 (fun g => mc X a₂ b₂ g • X₀) := h1p k r Wp A 5 _ X₀ hc2
  rw [hcB _ _ i1 i2, hBI k r Wp Wp D A hXi hA _ _ i1 i2 hI,
    integral_eq_zero_of_ae (hPh.mono fun p hp => by simp [hp]), mul_zero]

end ReciprocityTheory.ChartRestriction.DS.Mult1.TopH
