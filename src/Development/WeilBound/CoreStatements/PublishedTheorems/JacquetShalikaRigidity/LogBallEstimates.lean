module

public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.LogBallEstimates
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace LogBallEstimates

theorem neg_log_le {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) : -Real.log t ≤ t ^ (-ε) / ε := by
  have := Real.log_le_rpow_div (inv_pos.2 ht).le hε
  rwa [Real.log_inv, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le] at this

theorem large_power_bound {t σ c C : ℝ} {M : ℕ} (ht : 1 ≤ t) (hM : σ + 1 ≤ M) (hc : 0 ≤ c)
    (h : c ≤ C * (t ^ M)⁻¹) : c * t ^ σ ≤ |C| * min t t⁻¹ ^ (1 : ℝ) := by
  have t0 : 0 < t := by linarith
  rw [min_eq_right ((inv_le_one_of_one_le₀ ht).trans ht), Real.rpow_one]
  have h1 : t ^ σ * t ≤ t ^ M := by
    rw [← Real.rpow_add_one t0.ne', ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le ht hM
  have hp : 0 < t ^ M := by positivity
  have h2 : c ≤ |C| * (t ^ M)⁻¹ := h.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  have h3 : t ^ σ ≤ t ^ M * t⁻¹ := by
    rw [le_mul_inv_iff₀ t0]; exact h1
  calc c * t ^ σ ≤ |C| * (t ^ M)⁻¹ * t ^ σ := mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = |C| * ((t ^ M)⁻¹ * t ^ σ) := by ring
    _ ≤ |C| * ((t ^ M)⁻¹ * (t ^ M * t⁻¹)) := by gcongr
    _ = |C| * t⁻¹ := by field_simp

theorem big_log {t σ c C : ℝ} {M : ℕ} (ht : 1 ≤ t) (hM : σ + 2 ≤ M) (hc : 0 ≤ c)
    (h : c ≤ C * (t ^ M)⁻¹) : c * t ^ σ * |Real.log t| ≤ |C| * min t t⁻¹ ^ (1 : ℝ) := by
  have t0 : 0 < t := by linarith
  have hl : |Real.log t| ≤ t := by
    rw [abs_of_nonneg (Real.log_nonneg ht)]; linarith [Real.log_le_sub_one_of_pos t0]
  calc c * t ^ σ * |Real.log t| ≤ c * t ^ σ * t := by gcongr
    _ = c * t ^ (σ + 1) := by rw [Real.rpow_add_one t0.ne']; ring
    _ ≤ _ := large_power_bound ht (by linarith) hc h

theorem small_power_bound {t b ε c C : ℝ} (t0 : 0 < t) (t1 : t < 1) (hε : 0 < ε) (hb : 2 * ε ≤ b + 1)
    (hc : 0 ≤ c) (h : c ≤ C * t) : c * t ^ b ≤ |C| * t ^ (2 * ε) := by
  have h2 : c ≤ |C| * t := h.trans (mul_le_mul_of_nonneg_right (le_abs_self C) t0.le)
  calc c * t ^ b ≤ |C| * t * t ^ b := mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = |C| * t ^ (b + 1) := by rw [Real.rpow_add_one t0.ne']; ring
    _ ≤ |C| * t ^ (2 * ε) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge t0 t1.le hb) (abs_nonneg _)

theorem small0 {t b ε c C : ℝ} (t0 : 0 < t) (t1 : t < 1) (hε : 0 < ε) (hb : 2 * ε ≤ b + 1)
    (hc : 0 ≤ c) (h : c ≤ C * t) : c * t ^ b ≤ |C| * (1 + ε⁻¹) * min t t⁻¹ ^ ε := by
  rw [min_eq_left (t1.le.trans (one_le_inv₀ t0 |>.2 t1.le))]
  have h1 := small_power_bound t0 t1 hε hb hc h
  have h2 : t ^ (2 * ε) ≤ t ^ ε := Real.rpow_le_rpow_of_exponent_ge t0 t1.le (by linarith)
  have h3 : 0 ≤ |C| * t ^ ε * ε⁻¹ := by positivity
  calc c * t ^ b ≤ |C| * t ^ ε := h1.trans (by gcongr)
    _ ≤ |C| * t ^ ε + |C| * t ^ ε * ε⁻¹ := by linarith
    _ = |C| * (1 + ε⁻¹) * t ^ ε := by ring

theorem small_log {t b ε c C : ℝ} (t0 : 0 < t) (t1 : t < 1) (hε : 0 < ε) (hb : 2 * ε ≤ b + 1)
    (hc : 0 ≤ c) (h : c ≤ C * t) : c * t ^ b * |Real.log t| ≤ |C| * (1 + ε⁻¹) * min t t⁻¹ ^ ε := by
  rw [min_eq_left (t1.le.trans (one_le_inv₀ t0 |>.2 t1.le))]
  have h1 := small_power_bound t0 t1 hε hb hc h
  have hl : |Real.log t| ≤ t ^ (-ε) / ε := by
    rw [abs_of_neg (Real.log_neg t0 t1)]; exact neg_log_le t0 hε
  have e : t ^ (2 * ε) * (t ^ (-ε) / ε) = t ^ ε * ε⁻¹ := by
    rw [mul_div_assoc', ← Real.rpow_add t0, div_eq_mul_inv]; ring_nf
  have h3 : 0 ≤ |C| * t ^ ε := by positivity
  calc c * t ^ b * |Real.log t| ≤ |C| * t ^ (2 * ε) * (t ^ (-ε) / ε) := by
        gcongr
    _ = |C| * t ^ ε * ε⁻¹ := by rw [mul_assoc, e]; ring
    _ ≤ |C| * t ^ ε + |C| * t ^ ε * ε⁻¹ := by linarith
    _ = |C| * (1 + ε⁻¹) * t ^ ε := by ring

theorem bddBelow_support_primePowerComponent_coeff {t ε c C : ℝ} (t0 : 0 < t) (t1 : t < 1) (hc : 0 ≤ c) (h : c ≤ C) :
    c * t ^ ε ≤ |C| * min t t⁻¹ ^ ε := by
  rw [min_eq_left (t1.le.trans (one_le_inv₀ t0 |>.2 t1.le))]
  exact mul_le_mul_of_nonneg_right (h.trans (le_abs_self C)) (by positivity)

theorem re_lt_of_ball {s s₀ : ℂ} {r : ℝ} (hs : s ∈ Metric.ball s₀ r) : |s.re - s₀.re| < r := by
  rw [Metric.mem_ball, dist_eq_norm] at hs
  rw [← Complex.sub_re]; exact (Complex.abs_re_le_norm _).trans_lt hs

variable {X : Type*} [MeasurableSpace X]

theorem intg (ν : Measure X) (D : X → ℝ) (hD : ∀ x, 0 < D x) (hDm : Measurable D) (F : X → ℂ)
    (hF : AEStronglyMeasurable F ν) (s : ℂ) (g : X → ℝ) (hg : Integrable g ν)
    (h0 : ∀ᵐ x ∂ν, ‖F x‖ * D x ^ s.re ≤ g x) : Integrable (fun x => F x * (D x : ℂ) ^ s) ν :=
  hg.mono' (hF.mul ((Complex.measurable_ofReal.comp hDm).pow_const s).aestronglyMeasurable)
    (h0.mono fun x hx => by rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hD x)]; exact hx)

theorem diffAt (ν : Measure X) (D : X → ℝ) (hD : ∀ x, 0 < D x) (hDm : Measurable D) (F : X → ℂ)
    (hF : AEStronglyMeasurable F ν) (s₀ : ℂ) (r : ℝ) (hr : 0 < r) (g : X → ℝ) (hg : Integrable g ν)
    (h0 : ∀ᵐ x ∂ν, ‖F x‖ * D x ^ s₀.re ≤ g x)
    (hb : ∀ᵐ x ∂ν, ∀ s ∈ Metric.ball s₀ r, ‖F x‖ * D x ^ s.re * |Real.log (D x)| ≤ g x) :
    DifferentiableAt ℂ (fun s => ∫ x, F x * (D x : ℂ) ^ s ∂ν) s₀ := by
  have hDc : Measurable fun x => (D x : ℂ) := Complex.measurable_ofReal.comp hDm
  have hmeas : ∀ s : ℂ, AEStronglyMeasurable (fun x => F x * (D x : ℂ) ^ s) ν := fun s =>
    hF.mul (hDc.pow_const s).aestronglyMeasurable
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℂ) (μ := ν)
    (F := fun s x => F x * (D x : ℂ) ^ s) (F' := fun s x => F x * ((D x : ℂ) ^ s * Complex.log (D x)))
    (x₀ := s₀) (bound := g) (Metric.ball_mem_nhds s₀ hr) (Filter.Eventually.of_forall fun s => hmeas s)
    (intg ν D hD hDm F hF s₀ g hg h0)
    (hF.mul ((hDc.pow_const s₀).mul (Complex.measurable_log.comp hDc)).aestronglyMeasurable)
    (hb.mono fun x hx s hs => by
      rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hD x), ← Complex.ofReal_log (hD x).le,
        Complex.norm_real, Real.norm_eq_abs, ← mul_assoc]
      exact hx s hs)
    hg
    (Filter.Eventually.of_forall fun x s _ =>
      ((Complex.hasStrictDerivAt_const_cpow (Or.inl (Complex.ofReal_ne_zero.2 (hD x).ne'))).hasDerivAt.const_mul (F x)))
  exact this.2.differentiableAt

end LogBallEstimates

open LogBallEstimates in
theorem duality_diagonalClass_of_affineProperBaseChange : D0 → V1 → E1 → E2 := by
  intro hD0 hV1 hE1 E _ _ _ k μ _ hk β hβ H H₀ hG
  obtain ⟨hpos, -, hcont, -⟩ := hD0 E k
  have hmin := (hV1 E k μ hk β hβ).2.2
  have hE := hE1 E k μ hk β hβ H₀ hG.meas₀ hG.inv₀ hG.cen hG.bdd
  have hDm : Measurable (Dt : GA E k → ℝ) := hcont.measurable
  have hS : MeasurableSet {g : GA E k | Dt g < 1} := measurableSet_lt hDm measurable_const
  obtain ⟨C₀, hC₀⟩ := hG.bdd
  obtain ⟨C₁, hC₁⟩ := hG.small
  have hFm : Measurable fun g => (Dt g : ℂ) * H g - H₀ g :=
    ((Complex.measurable_ofReal.comp hDm).mul hG.meas).sub hG.meas₀

  have hAb : ∀ (σ : ℝ), ∃ g : GA E k → ℝ, IntegrableOn g {g | Dt g < 1}ᶜ (μ.withDensity β) ∧
      ∀ x, x ∈ {g : GA E k | Dt g < 1}ᶜ → ∀ τ, τ ≤ σ →
        ‖H x‖ * Dt x ^ τ ≤ g x ∧ ‖H x‖ * Dt x ^ τ * |Real.log (Dt x)| ≤ g x := by
    intro σ
    obtain ⟨C, hC⟩ := hG.big (⌈σ⌉₊ + 2)
    refine ⟨fun x => |C| * min (Dt x) (Dt x)⁻¹ ^ (1 : ℝ), ((hmin 1 one_pos).const_mul |C|).integrableOn,
      fun x hx τ hτ => ?_⟩
    have h1 : 1 ≤ Dt x := not_lt.1 hx
    have hM : τ + 2 ≤ ((⌈σ⌉₊ + 2 : ℕ) : ℝ) := by push_cast; linarith [Nat.le_ceil σ]
    exact ⟨large_power_bound h1 (by linarith) (norm_nonneg _) (hC x h1), big_log h1 hM (norm_nonneg _) (hC x h1)⟩
  have hBb : ∀ ε : ℝ, 0 < ε → ∃ g : GA E k → ℝ, IntegrableOn g {g | Dt g < 1} (μ.withDensity β) ∧
      ∀ x, x ∈ {g : GA E k | Dt g < 1} → ∀ b, 2 * ε ≤ b + 1 →
        ‖(Dt x : ℂ) * H x - H₀ x‖ * Dt x ^ b ≤ g x ∧
          ‖(Dt x : ℂ) * H x - H₀ x‖ * Dt x ^ b * |Real.log (Dt x)| ≤ g x := by
    intro ε hε
    refine ⟨fun x => |C₁| * (1 + ε⁻¹) * min (Dt x) (Dt x)⁻¹ ^ ε,
      ((hmin ε hε).const_mul (|C₁| * (1 + ε⁻¹))).integrableOn, fun x hx b hb => ?_⟩
    have h1 : Dt x < 1 := hx
    exact ⟨small0 (hpos x) h1 hε hb (norm_nonneg _) (hC₁ x h1),
      small_log (hpos x) h1 hε hb (norm_nonneg _) (hC₁ x h1)⟩
  let κ : ℂ := ((k : ℂ) * Module.finrank ℚ E)⁻¹ * ∫ g in band E k, H₀ g ∂μ.withDensity β
  let A : ℂ → ℂ := fun s => ∫ g in {g | Dt g < 1}ᶜ, H g * (Dt g : ℂ) ^ s ∂μ.withDensity β
  let B : ℂ → ℂ := fun s => ∫ g in {g | Dt g < 1}, ((Dt g : ℂ) * H g - H₀ g) * (Dt g : ℂ) ^ (s - 1)
    ∂μ.withDensity β
  have hA : ∀ s₀ : ℂ, DifferentiableAt ℂ A s₀ := by
    intro s₀
    obtain ⟨g, hg, hgb⟩ := hAb (s₀.re + 1)
    refine diffAt _ Dt hpos hDm H hG.meas.aestronglyMeasurable s₀ 1 one_pos g hg ?_ ?_
    · exact (ae_restrict_iff' hS.compl).2 (Eventually.of_forall fun x hx => (hgb x hx _ (by linarith)).1)
    · exact (ae_restrict_iff' hS.compl).2 (Eventually.of_forall fun x hx s hs =>
        (hgb x hx _ (by linarith [(abs_lt.1 (re_lt_of_ball hs)).2])).2)
  have hB : ∀ s₀ : ℂ, 0 < s₀.re → DifferentiableAt ℂ B s₀ := by
    intro s₀ h0
    obtain ⟨g, hg, hgb⟩ := hBb (s₀.re / 4) (by linarith)
    have := diffAt _ Dt hpos hDm _ hFm.aestronglyMeasurable (s₀ - 1) (s₀.re / 2) (by linarith) g hg
      ((ae_restrict_iff' hS).2 (Eventually.of_forall fun x hx =>
        (hgb x hx _ (by rw [Complex.sub_re, Complex.one_re]; linarith)).1))
      ((ae_restrict_iff' hS).2 (Eventually.of_forall fun x hx s hs =>
        (hgb x hx _ (by
          have := (abs_lt.1 (re_lt_of_ball hs)).1
          rw [Complex.sub_re, Complex.one_re] at this; linarith)).2))
    have h2 : DifferentiableAt ℂ (fun s : ℂ => s - 1) s₀ := differentiableAt_id.sub_const 1
    have h3 := DifferentiableAt.comp s₀ this h2
    exact h3
  refine ⟨fun s => (s - 1) * (A s + B s) + κ, fun s hs => ?_, fun s hs => ?_, fun hb => ?_⟩
  · have h2 : DifferentiableAt ℂ (fun s : ℂ => s - 1) s := differentiableAt_id.sub_const 1
    exact (h2.mul ((hA s).add (hB s hs))).add_const κ |>.differentiableWithinAt
  · obtain ⟨gA, hgA, hgAb⟩ := hAb s.re
    obtain ⟨gB, hgB, hgBb⟩ := hBb (1 / 2) (by norm_num)
    have i1 : IntegrableOn (fun g => H g * (Dt g : ℂ) ^ s) {g | Dt g < 1}ᶜ (μ.withDensity β) :=
      intg _ Dt hpos hDm H hG.meas.aestronglyMeasurable s gA hgA
        ((ae_restrict_iff' hS.compl).2 (Eventually.of_forall fun x hx => (hgAb x hx _ le_rfl).1))
    have i2 : IntegrableOn (fun g => ((Dt g : ℂ) * H g - H₀ g) * (Dt g : ℂ) ^ (s - 1)) {g | Dt g < 1}
        (μ.withDensity β) :=
      intg _ Dt hpos hDm _ hFm.aestronglyMeasurable (s - 1) gB hgB
        ((ae_restrict_iff' hS).2 (Eventually.of_forall fun x hx =>
          (hgBb x hx _ (by rw [Complex.sub_re, Complex.one_re]; linarith)).1))
    have hs1 : 0 < (s - 1).re := by rw [Complex.sub_re, Complex.one_re]; linarith
    have i3 : IntegrableOn (fun g => H₀ g * (Dt g : ℂ) ^ (s - 1)) {g | Dt g < 1} (μ.withDensity β) :=
      intg _ Dt hpos hDm _ hG.meas₀.aestronglyMeasurable (s - 1) _
        ((hmin _ hs1).const_mul |C₀|).integrableOn
        ((ae_restrict_iff' hS).2 (Eventually.of_forall fun x hx =>
          bddBelow_support_primePowerComponent_coeff (hpos x) hx (norm_nonneg _) (hC₀ x)))
    have hid : ∀ g, H g * (Dt g : ℂ) ^ s =
        ((Dt g : ℂ) * H g - H₀ g) * (Dt g : ℂ) ^ (s - 1) + H₀ g * (Dt g : ℂ) ^ (s - 1) := by
      intro g
      have h0 : (Dt g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hpos g).ne'
      rw [Complex.cpow_sub _ _ h0, Complex.cpow_one]
      field_simp
      ring
    have i4 : IntegrableOn (fun g => H g * (Dt g : ℂ) ^ s) {g | Dt g < 1} (μ.withDensity β) := by
      simp_rw [hid]; exact i2.add i3
    have hint : Integrable (fun g => H g * (Dt g : ℂ) ^ s) (μ.withDensity β) := by
      have := i4.union i1
      rwa [Set.union_compl_self, integrableOn_univ] at this
    have hE' := hE (s - 1) hs1
    rw [← integral_add_compl hS hint]
    have hsplit : ∫ g in {g | Dt g < 1}, H g * (Dt g : ℂ) ^ s ∂μ.withDensity β =
        B s + ∫ g in {g | Dt g < 1}, H₀ g * (Dt g : ℂ) ^ (s - 1) ∂μ.withDensity β := by
      simp_rw [hid]; exact integral_add i2 i3
    rw [hsplit]
    show (s - 1) * (A s + B s) + κ = _
    linear_combination -hE'
  · show (1 - 1) * (A 1 + B 1) + κ = 0
    simp only [sub_self, zero_mul, zero_add, κ, hb, mul_zero]

end PositivityTheory.AdelicQuotientData

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.EuclideanHeightMul
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace EuclideanHeightMul

open GroundTheory.Automorphic

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem euclid_add {F : Type*} [NormedField F] {n : ℕ} (y z : Fin n → F) :
    Reduction.euclidNorm (y + z) ≤ Reduction.euclidNorm y + Reduction.euclidNorm z := by
  have h : ∀ x : Fin n → F, Reduction.euclidNorm x = ‖(WithLp.toLp 2 x : PiLp 2 (fun _ : Fin n => F))‖ := by
    intro x; rw [PiLp.norm_eq_of_L2]; rfl
  rw [h, h, h, WithLp.toLp_add]
  exact norm_add_le _ _

theorem euclid_vecMul_near {F : Type*} [NormedField F] {n : ℕ} {M : Matrix (Fin n) (Fin n) F} {m : ℝ}
    (hm : 0 ≤ m) (hM : ∀ i j, ‖(M - 1) i j‖ ≤ m) (z : Fin n → F) :
    Reduction.euclidNorm (z ᵥ* M) ≤ (1 + √n * (n * m)) * Reduction.euclidNorm z := by
  have e : z ᵥ* M = z + z ᵥ* (M - 1) := by rw [Matrix.vecMul_sub, Matrix.vecMul_one]; abel
  rw [e]
  refine (euclid_add _ _).trans ?_
  have := Reduction.euclidNorm_vecMul_le hm hM z
  linarith

def Vn (m : ℝ) : Set (GA E k) :=
  {c | (∀ w : InfinitePlace E, ∀ i j,
      ‖((Reduction.infAt w c : Matrix (Fin k) (Fin k) w.Completion) - 1) i j‖ < m) ∧
    ∀ v, v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 E))) →
      Reduction.finAt v c ∈ GLnLocal.integralGL (v.adicCompletion E) k}

theorem Vn_mem {m : ℝ} (hm : 0 < m) : Vn (E := E) (k := k) m ∈ 𝓝 (1 : GA E k) := by
  have hinf : ∀ᶠ c in 𝓝 (1 : GA E k), ∀ w : InfinitePlace E, ∀ i j,
      ‖((Reduction.infAt w c : Matrix (Fin k) (Fin k) w.Completion) - 1) i j‖ < m := by
    refine Filter.eventually_all.2 fun w => Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
    have hc : Continuous fun c : GA E k =>
        ‖((Reduction.infAt w c : Matrix (Fin k) (Fin k) w.Completion) - 1) i j‖ := by
      simp only [Matrix.sub_apply]
      exact (((Reduction.continuous_GL_apply i j).comp (Reduction.continuous_infAt w)).sub continuous_const).norm
    have h1 : ‖((Reduction.infAt w (1 : GA E k) : Matrix (Fin k) (Fin k) w.Completion) - 1) i j‖ = 0 := by
      simp [Reduction.infAt]
    exact hc.continuousAt.eventually_lt continuousAt_const (by rw [h1]; exact hm)
  have hfin := (Reduction.isOpen_setOf_forall_not_mem_imp (K := E) (n := k) ∅).mem_nhds
    (fun v _ => by
      have h1 : Reduction.finAt v (1 : GA E k) = 1 := by
        have h := Reduction.finAt_mul (K := E) (n := k) v 1 1
        rw [mul_one] at h
        exact left_eq_mul.1 h
      rw [h1]; exact Subgroup.one_mem _)
  filter_upwards [hinf, hfin] with c h1 h2
  exact ⟨h1, h2⟩

theorem height_mul_le {m : ℝ} (hm : 0 ≤ m) {c : GA E k} (hc : c ∈ Vn m) (g : GA E k) {ξ : Fin k → E}
    (hξ : ξ ≠ 0) : Reduction.height (g * c) ξ ≤
      (∏ w : InfinitePlace E, (1 + √k * (k * m)) ^ w.mult) * Reduction.height g ξ := by
  have hy := Reduction.hasFiniteContent_height g hξ
  have e : Reduction.height (g * c) ξ = Reduction.adelicNorm
      ((Reduction.ratVec ξ ᵥ* (g : Matrix (Fin k) (Fin k) (Ad E))) ᵥ* (c : Matrix (Fin k) (Fin k) (Ad E))) := by
    rw [Reduction.height, Units.val_mul, ← Matrix.vecMul_vecMul]
  rw [e, Reduction.height]
  have := Reduction.adelicNorm_le_of_local (hy.vecMul c) hy (fun _ => 1 + √k * (k * m)) (fun _ => 1) ∅
    (fun w => ?_) (fun _ _ => rfl) (fun v => ?_)
  · simpa only [Finset.prod_empty, mul_one] using this
  · rw [Reduction.infComp_vecMul_GL]
    exact euclid_vecMul_near hm (fun i j => (hc.1 w i j).le) _
  · rw [Reduction.finComp_vecMul_GL, Reduction.norm_vecMul_integralGL v (hc.2 v (Finset.notMem_empty v)), one_mul]

theorem exists_m {s : ℝ} (hs : 1 < s) :
    ∃ m : ℝ, 0 < m ∧ (∏ w : InfinitePlace E, (1 + √k * (k * m)) ^ w.mult) ≤ s := by
  have hcont : Continuous fun m : ℝ => ∏ w : InfinitePlace E, (1 + √k * (k * m)) ^ w.mult := by
    fun_prop
  have hev : ∀ᶠ m in 𝓝 (0 : ℝ), (∏ w : InfinitePlace E, (1 + √k * (k * m)) ^ w.mult) < s :=
    hcont.continuousAt.eventually_lt continuousAt_const (by simpa using hs)
  obtain ⟨m, hm, h⟩ := hev.exists_gt
  exact ⟨m, hm, h.le⟩

end EuclideanHeightMul

namespace EuclideanHeightMul

open GroundTheory.Automorphic

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem ht_mul_le (hDpos : ∀ g : GA E k, 0 < Dt g) (hDmul : ∀ g h : GA E k, Dt (g * h) = Dt g * Dt h)
    (hDcont : Continuous (Dt : GA E k → ℝ)) {r : ℝ} (hr : 1 < r) :
    ∃ U ∈ 𝓝 (1 : GA E k), ∀ c ∈ U, ∀ g ξ, ξ ≠ 0 → ht (g * c) ξ ≤ r * ht g ξ := by
  have hs : 1 < √r := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt zero_le_one hr
  obtain ⟨m, hm, hprod⟩ := exists_m (E := E) (k := k) hs
  have hD1 : Dt (1 : GA E k) = 1 := by
    have h := hDmul 1 1
    rw [mul_one] at h
    exact (mul_left_cancel₀ (hDpos 1).ne' (h.symm.trans (mul_one _).symm))
  have hcont : ContinuousAt (fun c : GA E k => (Dt c ^ (k : ℝ)⁻¹)⁻¹) 1 :=
    ((hDcont.rpow_const (fun _ => Or.inr (by positivity))).inv₀
      (fun c => (Real.rpow_pos_of_pos (hDpos c) _).ne')).continuousAt
  have hev : ∀ᶠ c in 𝓝 (1 : GA E k), (Dt c ^ (k : ℝ)⁻¹)⁻¹ < √r :=
    hcont.eventually_lt continuousAt_const (by simpa [hD1] using hs)
  refine ⟨{c | c ∈ Vn m ∧ (Dt c ^ (k : ℝ)⁻¹)⁻¹ < √r}, Filter.inter_mem (Vn_mem hm) hev, ?_⟩
  rintro c ⟨hc, hc2⟩ g ξ hξ
  have h1 := height_mul_le hm.le hc g hξ
  have hh0 : 0 ≤ Reduction.height g ξ := Reduction.height_nonneg _ _
  have ha : 0 < Dt g ^ (k : ℝ)⁻¹ := Real.rpow_pos_of_pos (hDpos g) _
  have hb : 0 < Dt c ^ (k : ℝ)⁻¹ := Real.rpow_pos_of_pos (hDpos c) _
  have hs0 : 0 ≤ √r := Real.sqrt_nonneg r
  unfold ht
  rw [hDmul, Real.mul_rpow (hDpos g).le (hDpos c).le]
  have h2 : Reduction.height (g * c) ξ ≤ √r * Reduction.height g ξ :=
    h1.trans (mul_le_mul_of_nonneg_right hprod hh0)
  calc Reduction.height (g * c) ξ / (Dt g ^ (k : ℝ)⁻¹ * Dt c ^ (k : ℝ)⁻¹)
      = Reduction.height (g * c) ξ * (Dt c ^ (k : ℝ)⁻¹)⁻¹ / Dt g ^ (k : ℝ)⁻¹ := by
        field_simp
    _ ≤ (√r * Reduction.height g ξ) * √r / Dt g ^ (k : ℝ)⁻¹ := by
        gcongr
    _ = (√r * √r) * (Reduction.height g ξ / Dt g ^ (k : ℝ)⁻¹) := by ring
    _ = r * (Reduction.height g ξ / Dt g ^ (k : ℝ)⁻¹) := by
        rw [Real.mul_self_sqrt (by linarith : (0 : ℝ) ≤ r)]

theorem bdd (hpos : ∀ (g : GA E k) ξ, ξ ≠ 0 → 0 < ht g ξ) (g : GA E k) :
    BddBelow (Set.range fun ξ : {ξ : Fin k → E // ξ ≠ 0} => ht g ξ.1) :=
  ⟨0, by rintro _ ⟨ξ, rfl⟩; exact (hpos g ξ.1 ξ.2).le⟩

theorem dmin_le (hpos : ∀ (g : GA E k) ξ, ξ ≠ 0 → 0 < ht g ξ) (g : GA E k) {ξ : Fin k → E} (hξ : ξ ≠ 0) :
    dmin g ≤ ht g ξ :=
  ciInf_le (bdd hpos g) (⟨ξ, hξ⟩ : {ξ : Fin k → E // ξ ≠ 0})

theorem dmin_eq (hDpos : ∀ g : GA E k, 0 < Dt g) (hpos : ∀ (g : GA E k) ξ, ξ ≠ 0 → 0 < ht g ξ)
    (hk : 1 ≤ k) (g : GA E k) : ∃ x : Fin k → E, x ≠ 0 ∧ dmin g = ht g x := by
  obtain ⟨x, hx, h⟩ := Reduction.exists_height_min (K := E) hk g
  have : Nonempty {ξ : Fin k → E // ξ ≠ 0} := ⟨⟨x, hx⟩⟩
  refine ⟨x, hx, le_antisymm (dmin_le hpos g hx) (le_ciInf fun ξ => ?_)⟩
  exact div_le_div_of_nonneg_right (h ξ.1 ξ.2) (Real.rpow_nonneg (hDpos g).le _)

theorem dmin_mul_le (hDpos : ∀ g : GA E k, 0 < Dt g) (hpos : ∀ (g : GA E k) ξ, ξ ≠ 0 → 0 < ht g ξ)
    (hk : 1 ≤ k) {r : ℝ} {c : GA E k} (hc : ∀ g ξ, ξ ≠ 0 → ht (g * c) ξ ≤ r * ht g ξ) (g : GA E k) :
    dmin (g * c) ≤ r * dmin g := by
  obtain ⟨x, hx, e⟩ := dmin_eq hDpos hpos hk g
  rw [e]
  exact (dmin_le hpos _ hx).trans (hc g x hx)

end EuclideanHeightMul

open EuclideanHeightMul in
theorem firstCohomologyBound_of_boundaryBound : D0 → H0 → K1 := by
  intro hD hH E _ _ _ k hk
  obtain ⟨hDpos, hDmul, hDcont, -⟩ := hD E k
  obtain ⟨hpos, hrat, -, hcpt, -⟩ := hH E k
  have dpos : ∀ g : GA E k, 0 < dmin g := fun g => by
    obtain ⟨x, hx, e⟩ := dmin_eq hDpos hpos hk g
    rw [e]; exact hpos g x hx
  refine ⟨?_, dpos, fun g ξ hξ => dmin_le hpos g hξ, ?_, ?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun g₀ => tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
    · have hev : ∀ᶠ r in 𝓝 (1 : ℝ), r * a < dmin g₀ :=
        (continuous_id.mul continuous_const).continuousAt.eventually_lt continuousAt_const (by simpa using ha)
      obtain ⟨r, hr, hra⟩ := hev.exists_gt
      obtain ⟨U, hU, hUr⟩ := ht_mul_le hDpos hDmul hDcont hr
      have ht : Filter.Tendsto (fun g : GA E k => g⁻¹ * g₀) (𝓝 g₀) (𝓝 1) := by
        have h : Filter.Tendsto (fun g : GA E k => g⁻¹ * g₀) (𝓝 g₀) (𝓝 (g₀⁻¹ * g₀)) :=
          (continuous_inv.mul continuous_const).tendsto g₀
        rwa [inv_mul_cancel] at h
      filter_upwards [ht hU] with g hg
      have h := dmin_mul_le hDpos hpos hk (hUr _ hg) g
      rw [mul_inv_cancel_left] at h
      have : r * a < r * dmin g := by linarith
      exact lt_of_mul_lt_mul_left this (by linarith)
    · have hev : ∀ᶠ r in 𝓝 (1 : ℝ), r * dmin g₀ < b :=
        (continuous_id.mul continuous_const).continuousAt.eventually_lt continuousAt_const (by simpa using hb)
      obtain ⟨r, hr, hrb⟩ := hev.exists_gt
      obtain ⟨U, hU, hUr⟩ := ht_mul_le hDpos hDmul hDcont hr
      have ht : Filter.Tendsto (fun g : GA E k => g₀⁻¹ * g) (𝓝 g₀) (𝓝 1) := by
        have h : Filter.Tendsto (fun g : GA E k => g₀⁻¹ * g) (𝓝 g₀) (𝓝 (g₀⁻¹ * g₀)) :=
          (continuous_const.mul continuous_id).tendsto g₀
        rwa [inv_mul_cancel] at h
      filter_upwards [ht hU] with g hg
      have h := dmin_mul_le hDpos hpos hk (hUr _ hg) g₀
      rw [mul_inv_cancel_left] at h
      linarith
  · have hge : ∀ (γ : GL (Fin k) E) (g : GA E k), dmin g ≤ dmin (ratGL E k γ * g) := by
      intro γ g
      obtain ⟨x, hx, e⟩ := dmin_eq hDpos hpos hk (ratGL E k γ * g)
      rw [e, hrat]
      refine dmin_le hpos g fun h0 => hx ?_
      have := congrArg (· ᵥ* (γ⁻¹ : GL (Fin k) E).val) h0
      simpa [Matrix.vecMul_vecMul] using this
    intro γ g
    refine le_antisymm ?_ (hge γ g)
    have := hge γ⁻¹ (ratGL E k γ * g)
    rwa [map_inv, inv_mul_cancel_left] at this
  · intro C hC
    obtain ⟨B, hB⟩ := hcpt C hC
    refine ⟨max B 1, le_max_right _ _, fun c hc g => ?_⟩
    exact dmin_mul_le hDpos hpos hk (fun g ξ hξ =>
      (hB c hc g ξ hξ).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hpos g ξ hξ).le)) g
  · intro f hf M
    obtain ⟨C0, h0⟩ := hf 0
    obtain ⟨C1, h1⟩ := hf M
    refine ⟨max C0 C1, fun g => ?_⟩
    obtain ⟨x, hx, e⟩ := dmin_eq hDpos hpos hk g
    have a := h0 g x hx
    have b := h1 g x hx
    rw [pow_zero, mul_one] at a
    rw [← e] at b
    unfold wt
    by_cases hd : dmin g ≤ 1
    · rw [min_eq_right hd]
      exact b.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (dpos g).le M))
    · rw [min_eq_left (le_of_not_ge hd), one_pow, mul_one]
      exact a.trans (le_max_left _ _)

end PositivityTheory.AdelicQuotientData

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.SquareIntegralBound
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace SquareIntegralBound

theorem sqle (a b : ℝ≥0∞) : a * b ≤ a ^ 2 + b ^ 2 := by
  rcases le_total a b with h | h
  · calc a * b ≤ b * b := by gcongr
      _ = b ^ 2 := (sq b).symm
      _ ≤ a ^ 2 + b ^ 2 := le_add_self
  · calc a * b ≤ a * a := by gcongr
      _ = a ^ 2 := (sq a).symm
      _ ≤ a ^ 2 + b ^ 2 := le_self_add

theorem intMul {X : Type} [MeasurableSpace X] {ν : Measure X} {F G : X → ℂ}
    (hF : AEStronglyMeasurable F ν) (hG : AEStronglyMeasurable G ν)
    (hF2 : ∫⁻ x, ‖F x‖ₑ ^ 2 ∂ν < ∞) (hG2 : ∫⁻ x, ‖G x‖ₑ ^ 2 ∂ν < ∞) :
    Integrable (fun x => F x * conj (G x)) ν := by
  refine ⟨hF.mul (Complex.continuous_conj.comp_aestronglyMeasurable hG), ?_⟩
  unfold HasFiniteIntegral
  calc ∫⁻ x, ‖F x * conj (G x)‖ₑ ∂ν ≤ ∫⁻ x, (‖F x‖ₑ ^ 2 + ‖G x‖ₑ ^ 2) ∂ν := by
        refine lintegral_mono fun x => ?_
        rw [enorm_mul]
        have : ‖conj (G x)‖ₑ = ‖G x‖ₑ := by
          rw [← ofReal_norm, ← ofReal_norm, Complex.norm_conj]
        rw [this]; exact sqle _ _
    _ = ∫⁻ x, ‖F x‖ₑ ^ 2 ∂ν + ∫⁻ x, ‖G x‖ₑ ^ 2 ∂ν := lintegral_add_left' (hF.enorm.pow_const 2) _
    _ < ∞ := ENNReal.add_lt_top.2 ⟨hF2, hG2⟩

theorem bnd (D B C1 C2 s : ℝ) (N : ℕ) (hD : 0 < D) (hB : 0 ≤ B) (hs : 2 ≤ s) (hN : s + 1 ≤ N) (T : ℝ≥0∞)
    (h1 : T ≤ ENNReal.ofReal (C1 * D ^ (-1 : ℝ))) (h2 : T ≤ ENNReal.ofReal (C2 * D ^ (-(N : ℝ)))) :
    ENNReal.ofReal (B * D ^ s) * T ≤ ENNReal.ofReal (B * max (max C1 C2) 0 * min D D⁻¹ ^ (1 : ℝ)) := by
  set K := max (max C1 C2) 0 with hKdef
  have hK0 : 0 ≤ K := le_max_right _ _
  have hC1 : C1 ≤ K := le_trans (le_max_left _ _) (le_max_left _ _)
  have hC2 : C2 ≤ K := le_trans (le_max_right _ _) (le_max_left _ _)
  have hBs : 0 ≤ B * D ^ s := mul_nonneg hB (Real.rpow_nonneg hD.le _)
  rw [Real.rpow_one]
  rcases le_or_gt D 1 with hD1 | hD1
  · have hmin : min D D⁻¹ = D := min_eq_left (le_trans hD1 (one_le_inv₀ hD |>.mpr hD1))
    rw [hmin]
    calc ENNReal.ofReal (B * D ^ s) * T ≤ ENNReal.ofReal (B * D ^ s) * ENNReal.ofReal (C1 * D ^ (-1 : ℝ)) :=
          by gcongr
      _ = ENNReal.ofReal (B * D ^ s * (C1 * D ^ (-1 : ℝ))) := (ENNReal.ofReal_mul hBs).symm
      _ ≤ ENNReal.ofReal (B * K * D) := by
          apply ENNReal.ofReal_le_ofReal
          have e : D ^ s * D ^ (-1 : ℝ) = D ^ (s - 1) := by rw [← Real.rpow_add hD]; ring_nf
          have hP0 : 0 ≤ D ^ (s - 1) := Real.rpow_nonneg hD.le _
          have hPD : D ^ (s - 1) ≤ D := by
            calc D ^ (s - 1) ≤ D ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hD hD1 (by linarith)
              _ = D := Real.rpow_one D
          calc B * D ^ s * (C1 * D ^ (-1 : ℝ)) = B * C1 * (D ^ s * D ^ (-1 : ℝ)) := by ring
            _ = B * C1 * D ^ (s - 1) := by rw [e]
            _ ≤ B * K * D ^ (s - 1) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC1 hB) hP0
            _ ≤ B * K * D := mul_le_mul_of_nonneg_left hPD (mul_nonneg hB hK0)
  · have hmin : min D D⁻¹ = D⁻¹ := min_eq_right (le_trans (inv_le_one_of_one_le₀ hD1.le) hD1.le)
    rw [hmin]
    calc ENNReal.ofReal (B * D ^ s) * T ≤ ENNReal.ofReal (B * D ^ s) * ENNReal.ofReal (C2 * D ^ (-(N : ℝ))) :=
          by gcongr
      _ = ENNReal.ofReal (B * D ^ s * (C2 * D ^ (-(N : ℝ)))) := (ENNReal.ofReal_mul hBs).symm
      _ ≤ ENNReal.ofReal (B * K * D⁻¹) := by
          apply ENNReal.ofReal_le_ofReal
          have e : D ^ s * D ^ (-(N : ℝ)) = D ^ (s - N) := by rw [← Real.rpow_add hD]; ring_nf
          have hP0 : 0 ≤ D ^ (s - N) := Real.rpow_nonneg hD.le _
          have hPD : D ^ (s - N) ≤ D⁻¹ := by
            calc D ^ (s - N) ≤ D ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hD1.le (by linarith)
              _ = D⁻¹ := Real.rpow_neg_one D
          calc B * D ^ s * (C2 * D ^ (-(N : ℝ))) = B * C2 * (D ^ s * D ^ (-(N : ℝ))) := by ring
            _ = B * C2 * D ^ (s - N) := by rw [e]
            _ ≤ B * K * D ^ (s - N) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC2 hB) hP0
            _ ≤ B * K * D⁻¹ := mul_le_mul_of_nonneg_left hPD (mul_nonneg hB hK0)

end SquareIntegralBound

open SquareIntegralBound in
theorem moderate_growth_of : D0 → N0 → P2 → U0 → U2 → V1 → ThetaDecaying → M0 := by
  intro hD0 hN0 hP2 hU0 hU2 hV1 hG4 E _ _ _ k μ _ hk β hβ ψ hψ S m α α' u f φ hd
  obtain ⟨β₁, hβ₁, hU0a, hU0b⟩ := hU0 E k μ hk β hβ
  obtain ⟨β', hβ', hU2'⟩ := hU2 E k μ ψ hψ (k - 1) (by omega) β₁ hβ₁
  obtain ⟨hDpos, hDmul, hDcont, hDrat, hDU, -⟩ := hD0 E k
  obtain ⟨-, -, -, -, hPchi, hGoodPre, hLu, hLmir, hLcont, hLsupp⟩ := hP2 E k ψ hψ
  obtain ⟨C, hC, hfC⟩ := hd.supp
  obtain ⟨a, ε, Cf, hε, hsq⟩ := hd.sq
  obtain ⟨Φ₀, hΦ1, -, hΦc, hΦI⟩ :=
    exists_continuous_one_zero_of_isCompact hC isClosed_empty (Set.disjoint_empty C)
  obtain ⟨-, -, hV1c⟩ := hV1 E k μ hk β hβ
  have hk1 : k - 1 < k := by omega
  have hDu : ∀ u g : GA E k, UU 0 u → Dt (u * g) = Dt g := fun u g hu => by
    rw [hDmul, hDU 0 u hu, one_mul]
  have hDr : ∀ γ (g : GA E k), Dt (ratGL E k γ * g) = Dt g := fun γ g => by
    rw [hDmul, hDrat, one_mul]
  obtain ⟨Bφ, hBφ⟩ : ∃ B, ∀ g, ‖φ g‖ ≤ B := by
    obtain ⟨B, hB⟩ := hd.dec 0
    have hne : (fun _ => (1 : E) : Fin k → E) ≠ 0 := fun h => by
      have := congrFun h ⟨0, hk⟩; simp at this
    exact ⟨B, fun g => by simpa using hB g _ hne⟩
  have hBφ0 : 0 ≤ Bφ := (norm_nonneg _).trans (hBφ 1)
  refine ⟨β', a / 2 + 1, hβ', fun z hz => ?_⟩
  set χ₁ : GA E k → ℂ := fun g => ((Dt g ^ (a / 2) : ℝ) : ℂ) with hχ₁
  set χ₂ : GA E k → ℂ := fun g => conj ((Dt g : ℂ) ^ (z - ((a / 2 : ℝ) : ℂ))) * (Φ₀ (lastRow g) : ℂ) with hχ₂
  have hχ₁c : Continuous χ₁ := Complex.continuous_ofReal.comp
    (hDcont.rpow_const fun g => Or.inl (hDpos g).ne')
  have hχ₂c : Continuous χ₂ := by
    refine (Complex.continuous_conj.comp ?_).mul (Complex.continuous_ofReal.comp (Φ₀.continuous.comp hLcont))
    exact (Complex.continuous_ofReal.comp hDcont).cpow continuous_const
      fun g => Complex.ofReal_mem_slitPlane.2 (hDpos g)
  have hχ₁u : ∀ u, UU 0 u → ∀ g, χ₁ (u * g) = χ₁ g := fun u hu g => by simp only [hχ₁, hDu u g hu]
  have hχ₁m : ∀ γ, IsMir (k - 1) γ → ∀ g, χ₁ (ratGL E k γ * g) = χ₁ g := fun γ _ g => by simp only [hχ₁, hDr]
  have hχ₂u : ∀ u, UU 0 u → ∀ g, χ₂ (u * g) = χ₂ g := fun u hu g => by simp only [hχ₂, hDu u g hu, hLu u g hu]
  have hχ₂m : ∀ γ, IsMir (k - 1) γ → ∀ g, χ₂ (ratGL E k γ * g) = χ₂ g := fun γ hγ g => by
    simp only [hχ₂, hDr, hLmir γ g (by simpa using hγ)]
  obtain ⟨hpre1, hwf, -⟩ := hPchi (k - 1) hk1 f χ₁ hd.pre hχ₁c hχ₁u hχ₁m
  obtain ⟨hpre2, hwφ, hgood2⟩ := hPchi (k - 1) hk1 φ χ₂ (hGoodPre _ _ hd.good) hχ₂c hχ₂u hχ₂m
  have hgood2 := hgood2 hd.good
  have hK : ∀ g, lastRow g ∈ C → χ₁ g * conj (χ₂ g) = (Dt g : ℂ) ^ z := fun g hg => by
    have h1 : Φ₀ (lastRow g) = 1 := hΦ1 hg
    simp only [hχ₁, hχ₂, map_mul, Complex.conj_conj, Complex.conj_ofReal, h1, Complex.ofReal_one, mul_one]
    rw [Complex.ofReal_cpow (hDpos g).le, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 (hDpos g).ne')]
    congr 1; ring
  have hW : ∀ g, whit ψ (k - 1) (fun g => χ₁ g * f g) g * conj (whit ψ (k - 1) (fun g => χ₂ g * φ g) g) =
      PW ψ f φ g * (Dt g : ℂ) ^ z := fun g => by
    rw [hwf, hwφ]
    by_cases h0 : whit ψ (k - 1) f g = 0
    · simp [PW, h0]
    · rw [PW, ← hK g (hLsupp (k - 1) hk1 f C hfC g h0), map_mul]; ring
  have hF : ∀ g, χ₁ g * f g * conj (χ₂ g * φ g) = f g * conj (φ g) * (Dt g : ℂ) ^ z := fun g => by
    by_cases h0 : f g = 0
    · simp [h0]
    · rw [← hK g (hfC g h0), map_mul]; ring
  have hL2f : ∫⁻ g, ‖χ₁ g * f g‖ₑ ^ 2 ∂μ.withDensity β₁ < ∞ := by
    rw [hU0a (fun g => ‖χ₁ g * f g‖ₑ ^ 2) (hpre1.cont.measurable.enorm.pow_const 2)
      (fun γ hγ g => congrArg (fun w : ℂ => ‖w‖ₑ ^ 2) (hpre1.left γ hγ g))]
    refine lt_of_le_of_lt (lintegral_mono fun g => ?_) (((hV1c ε hε).const_mul Cf).lintegral_lt_top)
    have hterm : ∀ x, ‖χ₁ x * f x‖ₑ ^ 2 = ENNReal.ofReal (Dt x ^ a) * ‖f x‖ₑ ^ 2 := fun x => by
      rw [enorm_mul, mul_pow]
      congr 1
      rw [hχ₁]
      simp only
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (hDpos x).le _),
        ← ENNReal.ofReal_pow (Real.rpow_nonneg (hDpos x).le _), ← Real.rpow_mul_natCast (hDpos x).le]
      norm_num
    simp only [hterm, hDr, ENNReal.tsum_mul_left]
    calc ENNReal.ofReal (Dt g ^ a) * ∑' ξ : RowT E k k, ‖f (ratGL E k (gam ξ) * g)‖ₑ ^ 2
        ≤ ENNReal.ofReal (Dt g ^ a) * ENNReal.ofReal (Cf * min (Dt g) (Dt g)⁻¹ ^ ε * Dt g ^ (-a)) := by
          gcongr; exact hsq g
      _ = ENNReal.ofReal (Cf * min (Dt g) (Dt g)⁻¹ ^ ε) := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (hDpos g).le _)]
        congr 1
        have hp := Real.rpow_pos_of_pos (hDpos g) a
        rw [Real.rpow_neg (hDpos g).le]
        field_simp
  have hL2φ : ∫⁻ g, ‖χ₂ g * φ g‖ₑ ^ 2 ∂μ.withDensity β₁ < ∞ := by
    obtain ⟨-, hG4b⟩ := hG4 E k hk φ hd.dec
    obtain ⟨s, hs⟩ : ∃ s, s = 2 * z.re - a := ⟨_, rfl⟩
    have hs2 : 2 ≤ s := by linarith
    obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ⌈s⌉₊ + 1 := ⟨_, rfl⟩
    have hNs : s + 1 ≤ (N : ℝ) := by rw [hN]; push_cast; linarith [Nat.le_ceil s]
    obtain ⟨C1, hC1⟩ := hG4b _ hΦc.isCompact k le_rfl
    obtain ⟨C2, hC2⟩ := hG4b _ hΦc.isCompact (k * N) (Nat.le_mul_of_pos_right k (by omega))
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have e1 : -((k : ℕ) : ℝ) / k = -1 := by field_simp
    have e2 : -(((k * N : ℕ)) : ℝ) / k = -(N : ℝ) := by push_cast; field_simp
    rw [e1] at hC1; rw [e2] at hC2
    rw [hU0a (fun g => ‖χ₂ g * φ g‖ₑ ^ 2) (hpre2.cont.measurable.enorm.pow_const 2)
      (fun γ hγ g => congrArg (fun w : ℂ => ‖w‖ₑ ^ 2) (hpre2.left γ hγ g))]
    refine lt_of_le_of_lt (lintegral_mono fun g => ?_)
      (((hV1c 1 one_pos).const_mul (Bφ * max (max C1 C2) 0)).lintegral_lt_top)
    refine le_trans ?_ (SquareIntegralBound.bnd (Dt g) Bφ C1 C2 s N (hDpos g) hBφ0 hs2 hNs _ (hC1 g) (hC2 g))
    rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun ξ => ?_
    have hφ : ∀ γ g, φ (ratGL E k γ * g) = φ g := hd.inv
    rw [hφ]
    have hDx : Dt (ratGL E k (gam ξ) * g) = Dt g := hDr _ _
    by_cases hx : lastRow (ratGL E k (gam ξ) * g) ∈ tsupport Φ₀
    · rw [Set.indicator_of_mem hx, one_mul]
      rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
        ← ENNReal.ofReal_mul (mul_nonneg hBφ0 (Real.rpow_nonneg (hDpos g).le _))]
      refine ENNReal.ofReal_le_ofReal ?_
      have hχn : ‖χ₂ (ratGL E k (gam ξ) * g)‖ ≤ Dt g ^ (z.re - a / 2) := by
        rw [hχ₂]; simp only
        rw [norm_mul, Complex.norm_conj, Complex.norm_cpow_eq_rpow_re_of_pos (hDpos _), Complex.norm_real, hDx]
        simp only [Complex.sub_re, Complex.ofReal_re]
        have h0 := hΦI (lastRow (ratGL E k (gam ξ) * g))
        rw [Real.norm_of_nonneg h0.1]
        exact mul_le_of_le_one_right (Real.rpow_nonneg (hDpos g).le _) h0.2
      have hsq' : Dt g ^ s = (Dt g ^ (z.re - a / 2)) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (hDpos g).le]; congr 1; rw [hs]; push_cast; ring
      rw [norm_mul, mul_pow, hsq']
      have hφg := hBφ g
      have h3 : ‖χ₂ (ratGL E k (gam ξ) * g)‖ ^ 2 ≤ (Dt g ^ (z.re - a / 2)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hχn 2
      have h4 : 0 ≤ (Dt g ^ (z.re - a / 2)) ^ 2 := by positivity
      nlinarith [norm_nonneg (φ g), mul_le_mul_of_nonneg_right h3 (sq_nonneg ‖φ g‖),
        mul_le_mul_of_nonneg_left hφg (mul_nonneg h4 (norm_nonneg (φ g)))]
    · have : Φ₀ (lastRow (ratGL E k (gam ξ) * g)) = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [hχ₂, this]
  obtain ⟨hint, heq⟩ := hU2' _ _ hpre1 hgood2 hL2f hL2φ
  have hmeas : Measurable fun g => χ₁ g * f g * conj (χ₂ g * φ g) :=
    (hpre1.cont.mul (Complex.continuous_conj.comp hpre2.cont)).measurable
  have hinv : ∀ γ, IsMir (k - 1) γ → ∀ g, (fun g => χ₁ g * f g * conj (χ₂ g * φ g)) (ratGL E k γ * g) =
      (fun g => χ₁ g * f g * conj (χ₂ g * φ g)) g := fun γ hγ g => by
    have h1 := hpre1.left γ hγ g
    have h2 := hpre2.left γ hγ g
    simp only at h1 h2 ⊢
    rw [h1, h2]
  have hintF : Integrable (fun g => χ₁ g * f g * conj (χ₂ g * φ g)) (μ.withDensity β₁) :=
    intMul hpre1.cont.aestronglyMeasurable hpre2.cont.aestronglyMeasurable hL2f hL2φ
  have hsum : ∀ g, sumF (fun g => χ₁ g * f g * conj (χ₂ g * φ g)) g =
      sumF f g * conj (φ g) * (Dt g : ℂ) ^ z := fun g => by
    have hφ : ∀ γ g, φ (ratGL E k γ * g) = φ g := hd.inv
    simp only [sumF, hF]
    simp only [hφ, hDr, tsum_mul_right]
  refine ⟨hint.congr (Filter.Eventually.of_forall hW), ?_⟩
  calc ∫ g, sumF f g * conj (φ g) * (Dt g : ℂ) ^ z ∂μ.withDensity β
      = ∫ g, sumF (fun g => χ₁ g * f g * conj (χ₂ g * φ g)) g ∂μ.withDensity β := by simp only [hsum]
    _ = ∫ g, χ₁ g * f g * conj (χ₂ g * φ g) ∂μ.withDensity β₁ := (hU0b _ hmeas hinv hintF).symm
    _ = _ := heq
    _ = ∫ g, PW ψ f φ g * (Dt g : ℂ) ^ z ∂μ.withDensity β' := by simp only [hW]

end PositivityTheory.AdelicQuotientData

end
end
