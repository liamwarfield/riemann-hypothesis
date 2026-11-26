module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Lagr
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.MollId

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ContinuousCexpIp
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.StepB
noncomputable section

open MeasureTheory Filter Topology

namespace PositivityTheory.Rg.Sw.WR.D.Moll

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D

variable {n : ℕ} {X : Type} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

set_option maxHeartbeats 1000000 in
theorem step_b (Ψ : X → ℂ) (qq : X → E n) (hΨ : Integrable Ψ μ) (hqq : Measurable qq) (t ε : ℝ) (hε : 0 < ε)
    (ψ : E n → ℂ) (hψc : Continuous ψ) (hψi : Integrable ψ) (C : ℂ) :
    ∫ β, ψ β * (C * (∫ x, Ψ x * kr ε t (qq x - β) ∂μ)) =
      ∫ x, Ψ x * (∫ β, ψ β * (C * kr ε t (qq x - β))) ∂μ := by
  have hm : Measurable (fun p : E n × X => kr ε t (qq p.2 - p.1)) :=
    (continuous_kr ε t hε).measurable.comp ((hqq.comp measurable_snd).sub measurable_fst)
  have hs : AEStronglyMeasurable (fun p : E n × X => Ψ p.2) ((volume : Measure (E n)).prod μ) :=
    hΨ.aestronglyMeasurable.comp_snd
  have hψm : AEStronglyMeasurable (fun p : E n × X => ψ p.1) ((volume : Measure (E n)).prod μ) :=
    (hψc.measurable.comp measurable_fst).aestronglyMeasurable
  have hint : Integrable (fun p : E n × X => ψ p.1 * (C * (Ψ p.2 * kr ε t (qq p.2 - p.1))))
      ((volume : Measure (E n)).prod μ) := by
    refine Integrable.mono' ((hψi.norm.mul_prod hΨ.norm).mul_const (‖C‖ * ∫ y, ‖gam (n := n) ε y‖))
      (hψm.mul (aestronglyMeasurable_const.mul (hs.mul hm.aestronglyMeasurable))) ?_
    refine Eventually.of_forall fun p => ?_
    obtain ⟨β, x⟩ := p
    show ‖ψ β * (C * (Ψ x * kr ε t (qq x - β)))‖ ≤ ‖ψ β‖ * ‖Ψ x‖ * (‖C‖ * ∫ y, ‖gam (n := n) ε y‖)
    rw [norm_mul, norm_mul, norm_mul]
    have hk := norm_kr_le ε t hε (qq x - β)
    calc ‖ψ β‖ * (‖C‖ * (‖Ψ x‖ * ‖kr ε t (qq x - β)‖)) ≤
          ‖ψ β‖ * (‖C‖ * (‖Ψ x‖ * ∫ y, ‖gam (n := n) ε y‖)) := by gcongr
      _ = ‖ψ β‖ * ‖Ψ x‖ * (‖C‖ * ∫ y, ‖gam (n := n) ε y‖) := by ring
  have e1 : (fun β : E n => ψ β * (C * (∫ x, Ψ x * kr ε t (qq x - β) ∂μ))) =
      fun β => ∫ x, ψ β * (C * (Ψ x * kr ε t (qq x - β))) ∂μ := by
    funext β
    rw [← integral_const_mul, ← integral_const_mul]
  have e2 : (fun x : X => ∫ β : E n, ψ β * (C * (Ψ x * kr ε t (qq x - β)))) =
      fun x => Ψ x * (∫ β, ψ β * (C * kr ε t (qq x - β))) := by
    funext x
    rw [← integral_const_mul]
    congr 1
    funext β
    ring
  rw [e1, integral_integral_swap (f := fun (β : E n) (x : X) => ψ β * (C * (Ψ x * kr ε t (qq x - β)))) hint, e2]

end PositivityTheory.Rg.Sw.WR.D.Moll
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.StepC
noncomputable section

open MeasureTheory Filter Topology

namespace PositivityTheory.Rg.Sw.WR.D.Moll

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D

variable {n : ℕ} {X : Type} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

set_option maxHeartbeats 1000000 in
theorem step_c (ψ : E n → ℂ) (t ε : ℝ) (ht : t ≠ 0) (hε : 0 < ε) (w : E n) :
    ∫ β, ψ β * ((((|t| / (2 * Real.pi)) ^ (n ^ 2) : ℝ) : ℂ) * kr ε t (w - β)) =
      mM ψ (|t| / (2 * Real.sqrt ε)) w := by
  have hlpos : 0 < |t| / (2 * Real.sqrt ε) := div_pos (abs_pos.2 ht) (by have := Real.sqrt_pos.2 hε; positivity)
  set l := |t| / (2 * Real.sqrt ε) with hl
  have hk : ∀ u : E n, (((|t| / (2 * Real.pi)) ^ (n ^ 2) : ℝ) : ℂ) * kr ε t u =
      (((l ^ (n ^ 2) * gK (l • u)) : ℝ) : ℂ) := fun u => kraw_eq ε hε t ht u
  simp_rw [hk]
  have h1 : ∫ β, ψ β * (((l ^ (n ^ 2) * gK (l • (w - β))) : ℝ) : ℂ) =
      ∫ u, ψ (w - u) * (((l ^ (n ^ 2) * gK (l • u)) : ℝ) : ℂ) := by
    have := integral_sub_left_eq_self (μ := (volume : Measure (E n)))
      (fun u => ψ (w - u) * (((l ^ (n ^ 2) * gK (l • u)) : ℝ) : ℂ)) w
    simpa only [sub_sub_cancel] using this
  rw [h1]
  have h2 := Measure.integral_comp_smul (μ := (volume : Measure (E n))) (fun v : E n => ψ (w - l⁻¹ • v) * (gK v : ℂ)) l
  simp only [inv_smul_smul₀ hlpos.ne'] at h2
  rw [finrank_E] at h2
  unfold mM
  calc ∫ u, ψ (w - u) * (((l ^ (n ^ 2) * gK (l • u)) : ℝ) : ℂ)
      = ((l ^ (n ^ 2) : ℝ) : ℂ) * ∫ u, ψ (w - u) * (gK (l • u) : ℂ) := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        simp only
        push_cast
        ring
    _ = ((l ^ (n ^ 2) : ℝ) : ℂ) * (|(l ^ (n ^ 2))⁻¹| • ∫ v, ψ (w - l⁻¹ • v) * (gK v : ℂ)) := by rw [h2]
    _ = ∫ v, ψ (w - l⁻¹ • v) * (gK v : ℂ) := by
        rw [abs_of_pos (by positivity), Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
          mul_inv_cancel₀ (pow_pos hlpos _).ne', Complex.ofReal_one, one_mul]

end PositivityTheory.Rg.Sw.WR.D.Moll
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ExpCombine
noncomputable section

open MeasureTheory Filter Topology

namespace PositivityTheory.Rg.Sw.WR.D.Moll

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D

variable {n : ℕ} {X : Type} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

theorem exp_combine (t : ℝ) (y q β : E n) :
    Complex.exp (Complex.I * t * ip y q) * Complex.exp (-(Complex.I * t * ip β y)) =
      Complex.exp (Complex.I * t * ip y (q - β)) := by
  rw [ip_sub_right, ip_comm β y, ← Complex.exp_add]
  congr 1
  push_cast
  ring

set_option maxHeartbeats 1000000 in
theorem step_a (Ψ : X → ℂ) (qq : X → E n) (hΨ : Integrable Ψ μ) (hqq : Measurable qq) (t ε : ℝ) (hε : 0 < ε)
    (β : E n) :
    ∫ y, (∫ x, Ψ x * Complex.exp (Complex.I * t * ip y (qq x)) ∂μ) * gam ε y *
        Complex.exp (-(Complex.I * t * ip β y)) =
      ∫ x, Ψ x * kr ε t (qq x - β) ∂μ := by
  have hfun : ∀ (y : E n) (x : X), Ψ x * Complex.exp (Complex.I * t * ip y (qq x)) * gam ε y *
      Complex.exp (-(Complex.I * t * ip β y)) =
      Ψ x * (gam ε y * Complex.exp (Complex.I * t * ip y (qq x - β))) := by
    intro y x
    rw [← exp_combine]
    ring
  have hL : ∀ y : E n, (∫ x, Ψ x * Complex.exp (Complex.I * t * ip y (qq x)) ∂μ) * gam ε y *
      Complex.exp (-(Complex.I * t * ip β y)) =
      ∫ x, Ψ x * (gam ε y * Complex.exp (Complex.I * t * ip y (qq x - β))) ∂μ := by
    intro y
    rw [← integral_mul_const, ← integral_mul_const]
    exact integral_congr_ae (Eventually.of_forall fun x => hfun y x)
  have hm1 : Measurable fun p : E n × X => ip p.1 (qq p.2 - β) :=
    continuous_ip.measurable.comp (measurable_fst.prodMk ((hqq.comp measurable_snd).sub_const β))
  have hm2 : Measurable fun p : E n × X => Complex.exp (Complex.I * t * ip p.1 (qq p.2 - β)) :=
    ((Complex.measurable_ofReal.comp hm1).const_mul (Complex.I * t)).cexp
  have hint : Integrable (fun p : E n × X =>
      Ψ p.2 * (gam ε p.1 * Complex.exp (Complex.I * t * ip p.1 (qq p.2 - β))))
      ((volume : Measure (E n)).prod μ) := by
    refine Integrable.mono ((integrable_gauss (n := n) ε hε).mul_prod hΨ) ?_ ?_
    · exact (hΨ.1.comp_snd (μ := (volume : Measure (E n)))).mul
        ((((continuous_gam ε).measurable.comp measurable_fst).mul hm2).aestronglyMeasurable)
    · refine Eventually.of_forall fun p => ?_
      simp only [norm_mul, norm_cexp_It, mul_one]
      exact le_of_eq (mul_comm _ _)
  simp only [hL, kr, ← integral_const_mul]
  exact integral_integral_swap hint

end PositivityTheory.Rg.Sw.WR.D.Moll
end
end

noncomputable section

open MeasureTheory Filter Topology

namespace PositivityTheory.Rg.Sw.WR.D.Moll

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D

variable {n : ℕ} {X : Type} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

theorem continuous_cexp_ip (t : ℝ) : Continuous (fun p : E n × E n => Complex.exp (-(Complex.I * t * ip p.1 p.2))) :=
  Complex.continuous_exp.comp ((continuous_const.mul (Complex.continuous_ofReal.comp continuous_ip)).neg)

set_option maxHeartbeats 1000000 in
theorem lim_one (ρ : E n → ℂ) (hρ : Integrable ρ) (t : ℝ) (ψ : E n → ℂ) (hψc : Continuous ψ) (hψi : Integrable ψ)
    (C : ℂ) (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hε0 : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun k => ∫ β, ψ β * (C * ∫ y, ρ y * gam (ε k) y * Complex.exp (-(Complex.I * t * ip β y))))
      atTop (𝓝 (∫ β, ψ β * (C * ∫ y, ρ y * Complex.exp (-(Complex.I * t * ip β y))))) := by
  have hexp := continuous_cexp_ip (n := n) t
  have hbd : ∀ k y β, ‖ρ y * gam (ε k) y * Complex.exp (-(Complex.I * t * ip β y))‖ ≤ ‖ρ y‖ := by
    intro k y β
    rw [norm_mul, norm_mul, norm_cexp_neg_It, mul_one]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_gauss_le _ (hε k) y)
  have hcont : ∀ k, Continuous (fun β : E n => ∫ y, ρ y * gam (ε k) y * Complex.exp (-(Complex.I * t * ip β y))) := by
    intro k
    refine continuous_of_dominated (bound := fun y => ‖ρ y‖) ?_ ?_ hρ.norm ?_
    · intro β
      exact (hρ.aestronglyMeasurable.mul (continuous_gam (ε k)).aestronglyMeasurable).mul
        (hexp.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    · intro β; exact Eventually.of_forall fun y => hbd k y β
    · exact Eventually.of_forall fun y => by
        have hip : Continuous (fun β : E n => ip β y) := by
          unfold ip
          fun_prop
        have hy : Continuous (fun β : E n => Complex.exp (-(Complex.I * t * ip β y))) :=
          Complex.continuous_exp.comp ((continuous_const.mul (Complex.continuous_ofReal.comp hip)).neg)
        exact continuous_const.mul hy
  have hin : ∀ β : E n, Tendsto (fun k => ∫ y, ρ y * gam (ε k) y * Complex.exp (-(Complex.I * t * ip β y)))
      atTop (𝓝 (∫ y, ρ y * Complex.exp (-(Complex.I * t * ip β y)))) := by
    intro β
    refine tendsto_integral_of_dominated_convergence (fun y => ‖ρ y‖) ?_ hρ.norm ?_ ?_
    · intro k
      exact (hρ.aestronglyMeasurable.mul (continuous_gam (ε k)).aestronglyMeasurable).mul
        (hexp.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    · intro k; exact Eventually.of_forall fun y => hbd k y β
    · refine Eventually.of_forall fun y => ?_
      have h0 : Tendsto (fun k => -(((ε k * ip y y : ℝ)) : ℂ)) atTop (𝓝 0) := by
        have h := hε0.mul_const (ip y y)
        rw [zero_mul] at h
        have h' := ((Complex.continuous_ofReal.tendsto 0).comp h).neg
        simpa [Function.comp_def] using h'
      have hg : Tendsto (fun k => gam (ε k) y) atTop (𝓝 1) := by
        have := (Complex.continuous_exp.tendsto 0).comp h0
        simpa [gam, Function.comp_def] using this
      have := ((tendsto_const_nhds (x := ρ y)).mul hg).mul
        (tendsto_const_nhds (x := Complex.exp (-(Complex.I * t * ip β y))))
      simpa using this
  refine tendsto_integral_of_dominated_convergence (fun β => ‖ψ β‖ * (‖C‖ * ∫ y, ‖ρ y‖)) ?_
    (hψi.norm.mul_const _) ?_ ?_
  · intro k
    exact (hψc.mul (continuous_const.mul (hcont k))).aestronglyMeasurable
  · intro k; refine Eventually.of_forall fun β => ?_
    rw [norm_mul, norm_mul]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) (norm_nonneg _)
    exact norm_integral_le_of_norm_le hρ.norm (Eventually.of_forall fun y => hbd k y β)
  · exact Eventually.of_forall fun β => tendsto_const_nhds.mul (tendsto_const_nhds.mul (hin β))

set_option maxHeartbeats 1000000 in
theorem lim_two (Ψ : X → ℂ) (qq : X → E n) (hΨ : Integrable Ψ μ) (hqq : Measurable qq) (ψ : E n → ℂ)
    (hψc : Continuous ψ) (B : ℝ) (hB : ∀ x, ‖ψ x‖ ≤ B) (l : ℕ → ℝ) (hl : Tendsto (fun k => (l k)⁻¹) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, Ψ x * mM ψ (l k) (qq x) ∂μ) atTop (𝓝 (∫ x, ψ (qq x) * Ψ x ∂μ)) := by
  have hlim : ∫ x, ψ (qq x) * Ψ x ∂μ = ∫ x, Ψ x * ψ (qq x) ∂μ := by simp_rw [mul_comm]
  rw [hlim]
  refine tendsto_integral_of_dominated_convergence (fun x => ‖Ψ x‖ * B) ?_ (hΨ.norm.mul_const _) ?_ ?_
  · intro k
    exact hΨ.aestronglyMeasurable.mul ((continuous_mM ψ B hB hψc (l k)).measurable.comp hqq).aestronglyMeasurable
  · intro k; refine Eventually.of_forall fun x => ?_
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left (norm_mM_le ψ B hB hψc _ _) (norm_nonneg _)
  · exact Eventually.of_forall fun x => tendsto_const_nhds.mul (tendsto_mM ψ B hB hψc l hl (qq x))

set_option maxHeartbeats 1000000 in
theorem eq_A (Ψ : X → ℂ) (qq : X → E n) (hΨ : Integrable Ψ μ) (hqq : Measurable qq) (t : ℝ) (ht : t ≠ 0)
    (ψ : E n → ℂ) (hψc : Continuous ψ) (hψi : Integrable ψ) (ε : ℝ) (hε : 0 < ε) :
    ∫ β, ψ β * ((((|t| / (2 * Real.pi)) ^ (n ^ 2) : ℝ) : ℂ) *
        ∫ y, (∫ x, Ψ x * Complex.exp (Complex.I * t * ip y (qq x)) ∂μ) * gam ε y *
          Complex.exp (-(Complex.I * t * ip β y))) =
      ∫ x, Ψ x * mM ψ (|t| / (2 * Real.sqrt ε)) (qq x) ∂μ := by
  have ha : ∀ β : E n, ∫ y, (∫ x, Ψ x * Complex.exp (Complex.I * t * ip y (qq x)) ∂μ) * gam ε y *
      Complex.exp (-(Complex.I * t * ip β y)) = ∫ x, Ψ x * kr ε t (qq x - β) ∂μ :=
    fun β => step_a Ψ qq hΨ hqq t ε hε β
  simp_rw [ha]
  rw [step_b Ψ qq hΨ hqq t ε hε ψ hψc hψi]
  congr 1
  funext x
  rw [step_c ψ t ε ht hε (qq x)]

theorem _root_.PositivityTheory.Rg.Sw.WR.D.mollId : MollId := by
  intro n X _ μ _ Ψ qq hΨ hqq t ht hρ ψ hψc hψs
  obtain ⟨B, hB⟩ := hψc.bounded_above_of_compact_support hψs
  have hψi : Integrable ψ := hψc.integrable_of_hasCompactSupport hψs
  have hε : ∀ k : ℕ, 0 < 1 / ((k : ℝ) + 1) := fun k => by positivity
  have hε0 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hl : Tendsto (fun k : ℕ => (|t| / (2 * Real.sqrt (1 / ((k : ℝ) + 1))))⁻¹) atTop (𝓝 0) := by
    have e : (fun k : ℕ => (|t| / (2 * Real.sqrt (1 / ((k : ℝ) + 1))))⁻¹) =
        fun k : ℕ => (2 / |t|) * Real.sqrt (1 / ((k : ℝ) + 1)) := by
      funext k; rw [inv_div]; ring
    rw [e]
    have h := ((Real.continuous_sqrt.tendsto 0).comp hε0).const_mul (2 / |t|)
    simpa [Real.sqrt_zero, Function.comp_def] using h
  have h1 := lim_one _ hρ t ψ hψc hψi ((((|t| / (2 * Real.pi)) ^ (n ^ 2) : ℝ) : ℂ)) _ hε hε0
  have h2 := lim_two Ψ qq hΨ hqq ψ hψc B hB _ hl
  have e : (fun k : ℕ => ∫ β, ψ β * ((((|t| / (2 * Real.pi)) ^ (n ^ 2) : ℝ) : ℂ) *
        ∫ y, (∫ x, Ψ x * Complex.exp (Complex.I * t * ip y (qq x)) ∂μ) * gam (1 / ((k : ℝ) + 1)) y *
          Complex.exp (-(Complex.I * t * ip β y)))) =
      fun k : ℕ => ∫ x, Ψ x * mM ψ (|t| / (2 * Real.sqrt (1 / ((k : ℝ) + 1)))) (qq x) ∂μ := by
    funext k
    exact eq_A Ψ qq hΨ hqq t ht ψ hψc hψi _ (hε k)
  rw [e] at h1
  exact tendsto_nhds_unique h2 h1

end PositivityTheory.Rg.Sw.WR.D.Moll
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.DerivF
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.DerivFA
noncomputable section

open MeasureTheory Filter Topology

namespace PositivityTheory.Rg.Sw.WR.D

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR

variable {m n : ℕ}

theorem continuous_evXD (P : PX m n) : Continuous (evX P) := by
  unfold evX
  have h : Continuous fun x : Fin m → Fin n → ℂ =>
      (fun k : Fin m × Fin n × Bool => if k.2.2 then star (x k.1 k.2.1) else x k.1 k.2.1) := by
    refine continuous_pi fun k => ?_
    rcases k with ⟨a, i, b⟩
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact (continuous_apply i).comp (continuous_apply a)
    · simp only [↓reduceIte]
      exact continuous_star.comp ((continuous_apply i).comp (continuous_apply a))
  exact (MvPolynomial.continuous_eval P).comp h

theorem continuous_gsD (c : ℝ) : Continuous (gs (m := m) (n := n) c) := by
  have h : Continuous fun x : Fin m → Fin n → ℂ => (c * ∑ a, ∑ i, ‖x a i‖ ^ 2 : ℝ) := by fun_prop
  exact Complex.continuous_exp.comp (Complex.continuous_ofReal.comp h).neg

theorem continuous_ip_right (y : E n) : Continuous (fun q : E n => ip y q) := by
  unfold ip; fun_prop

theorem norm_exp_I_mul (t r : ℝ) : ‖Complex.exp (Complex.I * t * r)‖ = 1 := by
  have : Complex.I * (t : ℂ) * (r : ℂ) = ((t * r : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this]; exact Complex.norm_exp_ofReal_mul_I _

def pr (a b : Fin n) : E n →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) b).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Fin n → ℝ) a)

theorem pr_apply (a b : Fin n) (w : E n) : pr a b w = w a b := rfl

def Lc (q : E n) : E n →L[ℝ] ℂ := ∑ a, ∑ b, q a b • (Complex.ofRealCLM.comp (pr a b))

theorem Lc_apply (q w : E n) : Lc q w = ((ip w q : ℝ) : ℂ) := by
  simp only [Lc, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, pr_apply, ip, Complex.ofReal_sum, Complex.ofReal_mul, Complex.real_smul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem norm_Lc_le (q : E n) : ‖Lc q‖ ≤ ∑ a, ∑ b, |q a b| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  rw [Lc_apply, Complex.norm_real, Real.norm_eq_abs, ip, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  rw [abs_mul, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have h1 : ‖w a b‖ ≤ ‖w a‖ := norm_le_pi_norm (w a) b
  have h2 : ‖w a‖ ≤ ‖w‖ := norm_le_pi_norm w a
  rw [← Real.norm_eq_abs]; exact h1.trans h2

theorem continuous_Lc_comp {X : Type*} [TopologicalSpace X] {f : X → E n} (hf : Continuous f) :
    Continuous fun x => Lc (f x) := by
  unfold Lc
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_
  exact (((continuous_apply b).comp (continuous_apply a)).comp hf).smul
    (continuous_const : Continuous fun _ : X => Complex.ofRealCLM.comp (pr a b))

theorem abs_qX_le (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) (a b : Fin n) :
    |qX ε x a b| ≤ 2 * ‖evX (Qp ε a b) x‖ := by
  have h : qX ε x a b = (gramX ε x a b).re + (gramX ε x a b).im := rfl
  rw [h]
  have h1 := Complex.abs_re_le_norm (gramX ε x a b)
  have h2 := Complex.abs_im_le_norm (gramX ε x a b)
  have : gramX ε x a b = evX (Qp ε a b) x := rfl
  rw [← this]
  linarith [abs_add_le (gramX ε x a b).re (gramX ε x a b).im]

variable (ε : Fin m → Bool) (c t : ℝ)

def Fi (P : PX m n) (y : E n) (x : Fin m → Fin n → ℂ) : ℂ :=
  evX P x * gs c x * Complex.exp (Complex.I * t * ip y (qX ε x))

def Fd (P : PX m n) (y : E n) (x : Fin m → Fin n → ℂ) : E n →L[ℝ] ℂ :=
  (evX P x * gs c x * Complex.exp (Complex.I * t * ip y (qX ε x)) * (Complex.I * t)) • Lc (qX ε x)

variable {ε c t}

theorem continuous_Fi (hq : Continuous (qX (n := n) ε)) (P : PX m n) (y : E n) : Continuous (Fi ε c t P y) := by
  unfold Fi
  refine ((continuous_evXD P).mul (continuous_gsD c)).mul (Complex.continuous_exp.comp ?_)
  exact continuous_const.mul (Complex.continuous_ofReal.comp ((continuous_ip_right y).comp hq))

theorem continuous_Fd (hq : Continuous (qX (n := n) ε)) (P : PX m n) (y : E n) : Continuous (Fd ε c t P y) := by
  unfold Fd
  have h1 : Continuous fun x => evX P x * gs c x * Complex.exp (Complex.I * t * ip y (qX ε x)) * (Complex.I * t) :=
    (continuous_Fi hq P y).mul continuous_const
  exact h1.smul (continuous_Lc_comp hq)

theorem norm_Fi (P : PX m n) (y : E n) (x : Fin m → Fin n → ℂ) : ‖Fi ε c t P y x‖ = ‖evX P x * gs c x‖ := by
  unfold Fi; rw [norm_mul, norm_exp_I_mul, mul_one]

theorem integrable_Fi (hI : IntG) (hq : Continuous (qX (n := n) ε)) (hc : 0 < c) (P : PX m n) (y : E n) :
    Integrable (Fi ε c t P y) :=
  (hI m n c hc P).mono (continuous_Fi hq P y).aestronglyMeasurable
    (ae_of_all _ fun x => (norm_Fi P y x).le)

def bnd (ε : Fin m → Bool) (c t : ℝ) (P : PX m n) (x : Fin m → Fin n → ℂ) : ℝ :=
  |t| * ∑ a, ∑ b, 2 * ‖evX (Qp ε a b * P) x * gs c x‖

theorem integrable_bnd (hI : IntG) (hc : 0 < c) (P : PX m n) : Integrable (bnd ε c t P) := by
  unfold bnd
  refine Integrable.const_mul ?_ _
  refine integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => ?_
  exact ((hI m n c hc (Qp ε a b * P)).norm).const_mul 2

theorem norm_Fd_le (P : PX m n) (y : E n) (x : Fin m → Fin n → ℂ) : ‖Fd ε c t P y x‖ ≤ bnd ε c t P x := by
  have e0 : ‖Fd ε c t P y x‖ = ‖evX P x * gs c x‖ * |t| * ‖Lc (qX ε x)‖ := by
    simp only [Fd, norm_smul, norm_mul, norm_exp_I_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      one_mul, mul_one]
  rw [e0]
  unfold bnd
  calc ‖evX P x * gs c x‖ * |t| * ‖Lc (qX ε x)‖
      ≤ ‖evX P x * gs c x‖ * |t| * ∑ a, ∑ b, |qX ε x a b| :=
        mul_le_mul_of_nonneg_left (norm_Lc_le _) (by positivity)
    _ = |t| * ∑ a, ∑ b, ‖evX P x * gs c x‖ * |qX ε x a b| := by
        simp only [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_; ring
    _ ≤ |t| * ∑ a, ∑ b, 2 * ‖evX (Qp ε a b * P) x * gs c x‖ := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_) (abs_nonneg _)
        have h := abs_qX_le ε x a b
        have e : evX (Qp ε a b * P) x * gs c x = evX (Qp ε a b) x * (evX P x * gs c x) := by
          simp only [evX, map_mul]; ring
        rw [e]
        simp only [norm_mul]
        have hn : 0 ≤ ‖evX P x‖ * ‖gs c x‖ := by positivity
        nlinarith [mul_le_mul_of_nonneg_left h hn]

theorem hasFDerivAt_Fi (P : PX m n) (y : E n) (x : Fin m → Fin n → ℂ) :
    HasFDerivAt (fun y => Fi ε c t P y x) (Fd ε c t P y x) y := by
  have h1 : HasFDerivAt (fun y : E n => ((ip y (qX ε x) : ℝ) : ℂ)) (Lc (qX ε x)) y := by
    have : (fun y : E n => ((ip y (qX ε x) : ℝ) : ℂ)) = fun y => Lc (qX ε x) y :=
      funext fun y => (Lc_apply _ y).symm
    rw [this]; exact (Lc (qX ε x)).hasFDerivAt
  have h2 := (h1.const_mul (Complex.I * t)).cexp.const_mul (evX P x * gs c x)
  have e : (evX P x * gs c x) • Complex.exp (Complex.I * t * ((ip y (qX ε x) : ℝ) : ℂ)) • (Complex.I * t) • Lc (qX ε x)
      = Fd ε c t P y x := by
    rw [Fd, smul_smul, smul_smul, mul_assoc (evX P x * gs c x)]
  exact h2.congr_fderiv e

theorem hasFDerivAt_FP (hI : IntG) (hq : Continuous (qX (n := n) ε)) (hc : 0 < c) (P : PX m n) (y : E n) :
    HasFDerivAt (FP ε c t P) (∫ x, Fd ε c t P y x) y := by
  have := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume) (F := fun y x => Fi ε c t P y x)
    (F' := fun y x => Fd ε c t P y x) (x₀ := y) (bound := bnd ε c t P) (s := Set.univ) Filter.univ_mem
    (Eventually.of_forall fun y' => (continuous_Fi hq P y').aestronglyMeasurable) (integrable_Fi hI hq hc P y)
    (continuous_Fd hq P y).aestronglyMeasurable (ae_of_all _ fun x y' _ => norm_Fd_le P y' x)
    (integrable_bnd hI hc P) (ae_of_all _ fun x y' _ => hasFDerivAt_Fi P y' x)
  exact this

theorem integrable_Fd (hI : IntG) (hq : Continuous (qX (n := n) ε)) (hc : 0 < c) (P : PX m n) (y : E n) :
    Integrable (Fd ε c t P y) :=
  (integrable_bnd hI hc P).mono' (continuous_Fd hq P y).aestronglyMeasurable (ae_of_all _ fun x => norm_Fd_le P y x)

end PositivityTheory.Rg.Sw.WR.D
end
end

noncomputable section

open MeasureTheory Filter Topology

namespace PositivityTheory.Rg.Sw.WR.D

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR

variable {m n : ℕ} {ε : Fin m → Bool} {c t : ℝ}

theorem FP_eq_integral_Fi (P : PX m n) (y : E n) : FP ε c t P y = ∫ x, Fi ε c t P y x := rfl

theorem fderiv_FP_apply (hI : IntG) (hq : Continuous (qX (n := n) ε)) (hc : 0 < c) (P : PX m n) (y w : E n) :
    fderiv ℝ (FP ε c t P) y w = ∫ x, Fi ε c t P y x * (Complex.I * t) * ((ip w (qX ε x) : ℝ) : ℂ) := by
  rw [(hasFDerivAt_FP hI hq hc P y).fderiv, ContinuousLinearMap.integral_apply (integrable_Fd hI hq hc P y)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [Fd, ContinuousLinearMap.smul_apply, Lc_apply, smul_eq_mul, Fi]

theorem integrable_Fi_mul (hI : IntG) (hq : Continuous (qX (n := n) ε)) (hc : 0 < c) (P : PX m n) (y w : E n) :
    Integrable fun x => Fi ε c t P y x * (Complex.I * t) * ((ip w (qX ε x) : ℝ) : ℂ) := by
  have h := (integrable_Fd (t := t) hI hq hc P y).apply_continuousLinearMap w
  refine h.congr (ae_of_all _ fun x => ?_)
  simp only [Fd, ContinuousLinearMap.smul_apply, Lc_apply, smul_eq_mul, Fi]

theorem dirC_FP (hI : IntG) (hq : Continuous (qX (n := n) ε)) (hc : 0 < c) (P : PX m n)
    (v : Fin n → Fin n → ℂ) (y : E n) :
    dirC (FP ε c t P) v y =
      ∫ x, Fi ε c t P y x * (Complex.I * t) * ∑ a, ∑ b, v a b * (qX ε x a b : ℂ) := by
  unfold dirC
  rw [fderiv_FP_apply hI hq hc, fderiv_FP_apply hI hq hc, ← integral_const_mul,
    ← integral_add (integrable_Fi_mul hI hq hc P y _) ((integrable_Fi_mul hI hq hc P y _).const_mul _)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  have e : ∀ a b, v a b = ((v a b).re : ℂ) + Complex.I * ((v a b).im : ℂ) := fun a b => by
    rw [mul_comm]; exact (Complex.re_add_im (v a b)).symm
  simp only [ip, Complex.ofReal_sum, Complex.ofReal_mul]
  conv_rhs => rw [show (∑ a, ∑ b, v a b * (qX ε x a b : ℂ)) =
    ∑ a, ∑ b, (((v a b).re : ℂ) + Complex.I * ((v a b).im : ℂ)) * (qX ε x a b : ℂ) from
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [← e]]
  simp only [add_mul, Finset.sum_add_distrib, mul_add, Finset.mul_sum]
  ring_nf

theorem sum_ite_pair (k l : Fin n) (α : ℂ) (f : Fin n → Fin n → ℂ) :
    ∑ a, ∑ b, (if a = k ∧ b = l then α else 0) * f a b = α * f k l := by
  rw [Finset.sum_eq_single k, Finset.sum_eq_single l]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro a _ ha; simp [ha]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem sum_vkl (hA : AlgA) (k l : Fin n) (x : Fin m → Fin n → ℂ) :
    ∑ a, ∑ b, vkl k l a b * (qX ε x a b : ℂ) = evX (Qp ε k l) x := by
  have h := congrFun (congrFun ((hA m n ε).2.1 x) k) l
  have g : gramX ε x k l = evX (Qp ε k l) x := rfl
  rw [← g, ← h]
  simp only [vkl, add_mul, Finset.sum_add_distrib]
  rw [sum_ite_pair k l _ (fun a b => (qX ε x a b : ℂ)), sum_ite_pair l k _ (fun a b => (qX ε x a b : ℂ))]
  simp only [herm]
  push_cast
  ring

theorem Dkl_FP (hI : IntG) (hA : AlgA) (hc : 0 < c) (P : PX m n) (k l : Fin n) :
    Dkl k l (FP ε c t P) = FP ε c t (MvPolynomial.C (Complex.I * t) * Qp ε k l * P) := by
  have hq := (hA m n ε).2.2.2.2
  funext y
  unfold Dkl
  rw [dirC_FP hI hq hc]
  unfold FP
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  dsimp only
  rw [sum_vkl hA]
  simp only [Fi, evX, map_mul, MvPolynomial.eval_C]
  ring

theorem FP_add (hI : IntG) (hA : AlgA) (hc : 0 < c) (P Q : PX m n) :
    FP ε c t (P + Q) = FP ε c t P + FP ε c t Q := by
  have hq := (hA m n ε).2.2.2.2
  funext y
  simp only [Pi.add_apply]
  rw [FP_eq_integral_Fi, FP_eq_integral_Fi, FP_eq_integral_Fi,
    ← integral_add (integrable_Fi hI hq hc P y) (integrable_Fi hI hq hc Q y)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [Fi, evX, map_add (f := _)]; ring

theorem FP_C_mul (a : ℂ) (P : PX m n) :
    FP ε c t (MvPolynomial.C a * P) = a • FP ε c t P := by
  funext y
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [FP_eq_integral_Fi, FP_eq_integral_Fi, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [Fi, evX, map_mul, MvPolynomial.eval_C]; ring

theorem FP_sum (hI : IntG) (hA : AlgA) (hc : 0 < c) {ι : Type*} (s : Finset ι) (f : ι → PX m n) :
    FP ε c t (∑ i ∈ s, f i) = ∑ i ∈ s, FP ε c t (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    funext y
    simp only [Finset.sum_empty, Finset.sum_apply, Pi.zero_apply]
    rw [FP_eq_integral_Fi]
    simp [Fi, evX]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, FP_add hI hA hc, ih]

theorem foldr_FP (hI : IntG) (hA : AlgA) (hc : 0 < c) (σ : Equiv.Perm (Fin n)) (L : List (Fin n)) (P : PX m n) :
    L.foldr (fun k g => Dkl k (σ k) g) (FP ε c t P) =
      FP ε c t ((L.map fun k => MvPolynomial.C (Complex.I * t) * Qp ε k (σ k)).prod * P) := by
  induction L with
  | nil => simp
  | cons k L ih =>
    rw [List.foldr_cons, ih, Dkl_FP hI hA hc, List.map_cons, List.prod_cons]
    congr 1; ring

theorem sum_perm_eq_det :
    ∑ σ : Equiv.Perm (Fin n), MvPolynomial.C ((Equiv.Perm.sign σ : ℤ) : ℂ) *
      (((List.finRange n).map fun k => MvPolynomial.C (Complex.I * t) * Qp ε k (σ k)).prod)
      = MvPolynomial.C ((Complex.I * t) ^ n) * detQ ε := by
  have hprod : ∀ σ : Equiv.Perm (Fin n),
      ((List.finRange n).map fun k => MvPolynomial.C (Complex.I * t) * Qp ε k (σ k)).prod =
        MvPolynomial.C ((Complex.I * t) ^ n) * ∏ k, Qp ε k (σ k) := by
    intro σ
    rw [← Fin.prod_univ_def, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      map_pow]
  simp only [hprod]
  rw [detQ, ← Matrix.det_transpose, Matrix.det_apply', Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Matrix.transpose_apply, Matrix.of_apply]
  rw [show (MvPolynomial.C (((Equiv.Perm.sign σ : ℤ) : ℂ)) : PX m n) = (((Equiv.Perm.sign σ : ℤ) : PX m n)) by
    simp]
  ring

theorem Delta_FP (hI : IntG) (hA : AlgA) (hc : 0 < c) (P : PX m n) :
    Delta (FP ε c t P) = FP ε c t (MvPolynomial.C ((Complex.I * t) ^ n) * detQ ε * P) := by
  unfold Delta
  simp only [foldr_FP hI hA hc]
  rw [← sum_perm_eq_det (ε := ε) (t := t), Finset.sum_mul, FP_sum hI hA hc]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [mul_assoc, FP_C_mul]

theorem derivF_of (hI : IntG) (hA : AlgA) : DerivF := by
  intro m n ε c t hc P N
  have hq := (hA m n ε).2.2.2.2
  refine ⟨continuous_iff_continuousAt.2 fun y => (hasFDerivAt_FP hI hq hc P y).continuousAt, ?_⟩
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Function.iterate_succ_apply', ih, Delta_FP hI hA hc, pow_succ]
    congr 1; ring

theorem derivF : DerivF := derivF_of intG algA

end PositivityTheory.Rg.Sw.WR.D
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.CardAddB
noncomputable section

open MeasureTheory Filter Topology Metric

namespace PositivityTheory.Rg.Sw.WR.D

open PositivityTheory.Rg.Sw

theorem cardAddB {m : ℕ} (ε : Fin m → Bool) :
    (Finset.univ.filter fun a => ε a = true).card + (Finset.univ.filter fun a => ε a = false).card = m := by
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m))) (fun a => ε a = true)
  simpa using this

theorem nexpB (t r : ℝ) : ‖Complex.exp (-(Complex.I * t * r))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

theorem contIpB {n : ℕ} (y : E n) : Continuous fun β : E n => ip β y := by
  unfold ip
  fun_prop

theorem dens_of (hA : AlgA) (hI : IntG) (hD : DerivF) (hM : MollId) (hG : Gauss) (hCG : ClsGain)
    (hInt : Integr) : Dens := by
  intro m n ε c t hc ht P N hN
  obtain ⟨hTr, hHq, hHinv, hDet, hQc⟩ := hA m n ε
  have ht0 : t ≠ 0 := by
    rcases ht with rfl | rfl
    · exact hc.ne'
    · exact neg_ne_zero.mpr hc.ne'
  have hIt : (Complex.I * (t : ℂ)) ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr ht0)
  have hsec : ∀ (Q : PX m n) (y : E n), secN ε c t Q (herm y) = FP ε c t Q y := by
    intro Q y
    simp only [secN, FP, hTr]
  obtain ⟨P', hP'⟩ : ∃ P' : PX m n, P' = (MvPolynomial.C ((Complex.I * (t : ℂ)) ^ n) * detQ ε) ^ N * P := ⟨_, rfl⟩
  have hev : ∀ x : Fin m → Fin n → ℂ, evX P' x = ((Complex.I * (t : ℂ)) ^ n * (gramX ε x).det) ^ N * evX P x := by
    intro x
    rw [← hDet x, hP']
    simp only [evX, map_mul, map_pow, MvPolynomial.eval_C]
  have hDP' : Delta^[N] (FP ε c t P) = FP ε c t P' := by
    rw [hP']
    exact (hD m n ε c t hc P N).2
  have hFP'c : Continuous (FP ε c t P') := (hD m n ε c t hc P' N).1
  obtain ⟨R, hR⟩ := hG m n ε c t hc ht P
  have hpq := cardAddB ε
  generalize hp : (Finset.univ.filter fun i => ε i = true).card = p at hR hpq
  generalize hq : (Finset.univ.filter fun i => ε i = false).card = q at hR hpq
  have hs : ((t / c : ℝ) : ℂ) = 1 ∨ ((t / c : ℝ) : ℂ) = -1 := by
    rcases ht with rfl | rfl
    · left
      rw [div_self hc.ne']
      simp
    · right
      rw [neg_div, div_self hc.ne']
      simp
  obtain ⟨J, a, G, hGc, ⟨C, hC⟩, hGeq⟩ := hCG n _ hs p q N R
  have hFPcls : FP ε c t P = cls ((t / c : ℝ) : ℂ) 0 p q R := by
    funext y
    rw [← hsec]
    exact hR y
  have hFP'eq : ∀ y, FP ε c t P' y = ∑ j : Fin J, Polynomial.eval 0 (a j) * G j y := by
    intro y
    rw [← hDP', hFPcls, hGeq]
    simp
  have hbd : ∀ y, ‖FP ε c t P' y‖ ≤ (∑ j : Fin J, ‖Polynomial.eval 0 (a j)‖) * (C * dP y ^ (-((p + q + N : ℕ) : ℝ) / 2)) := by
    intro y
    rw [hFP'eq y, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC j y) (norm_nonneg _)
  have hσ : (n : ℝ) ^ 2 / 2 < ((p + q + N : ℕ) : ℝ) / 2 := by
    have h1 : ((n : ℝ)) ^ 2 < ((m + N : ℕ) : ℝ) := by exact_mod_cast hN
    rw [hpq]
    linarith
  have hFP'int : Integrable (FP ε c t P') volume := by
    refine Integrable.mono' (((hInt n).2 _ hσ).const_mul ((∑ j : Fin J, ‖Polynomial.eval 0 (a j)‖) * C)) hFP'c.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    calc ‖FP ε c t P' y‖ ≤ (∑ j : Fin J, ‖Polynomial.eval 0 (a j)‖) * (C * dP y ^ (-((p + q + N : ℕ) : ℝ) / 2)) := hbd y
      _ = (∑ j : Fin J, ‖Polynomial.eval 0 (a j)‖) * C * dP y ^ (-(((p + q + N : ℕ) : ℝ) / 2)) := by
        rw [neg_div]
        ring
  have hipc : ∀ β y : E n, ip β y = ip y β := by
    intro β y
    simp only [ip]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => mul_comm _ _
  have hcy : ∀ β : E n, Continuous fun y : E n => ip β y := fun β => (contIpB β).congr (fun y => hipc y β)
  have hhc : Continuous fun β : E n => herm β := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [herm]
    fun_prop
  have hdc : Continuous fun β : E n => (herm β).det := hhc.matrix_det
  have hDc : Continuous fun β : E n => ((Complex.I * (t : ℂ)) ^ n * (herm β).det) ^ N := (continuous_const.mul hdc).pow N
  have hF : Continuous fun β : E n => ∫ y : E n, FP ε c t P' y * Complex.exp (-(Complex.I * (t : ℂ) * (ip β y : ℂ))) := by
    refine continuous_of_dominated (bound := fun y => ‖FP ε c t P' y‖) (fun β => ?_) (fun β => Filter.Eventually.of_forall fun y => ?_) hFP'int.norm (Filter.Eventually.of_forall fun y => ?_)
    · exact hFP'c.aestronglyMeasurable.mul (Complex.continuous_exp.comp ((continuous_const.mul (Complex.continuous_ofReal.comp (hcy β))).neg)).aestronglyMeasurable
    · rw [norm_mul, nexpB, mul_one]
    · exact continuous_const.mul (Complex.continuous_exp.comp ((continuous_const.mul (Complex.continuous_ofReal.comp (contIpB y))).neg))
  obtain ⟨g, hg⟩ : ∃ g : E n → ℂ, g = fun β => (((Complex.I * (t : ℂ)) ^ n * (herm β).det) ^ N)⁻¹ * ((((|t| / (2 * Real.pi)) ^ n ^ 2 : ℝ) : ℂ) * ∫ y : E n, FP ε c t P' y * Complex.exp (-(Complex.I * (t : ℂ) * (ip β y : ℂ)))) := ⟨_, rfl⟩
  have hgU : ContinuousOn g {y : E n | (herm y).det ≠ 0} := by
    rw [hg]
    refine ContinuousOn.mul ?_ (continuous_const.mul hF).continuousOn
    exact hDc.continuousOn.inv₀ (fun β hβ => pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hIt) hβ))
  have hgm : Measurable g := by
    rw [hg]
    exact hDc.measurable.inv.mul (continuous_const.mul hF).measurable
  have hcan : ∀ u v w D : ℂ, D ≠ 0 → u * (v * w) = u * D⁻¹ * (D * v * w) := by
    intro u v w D hD
    rw [show u * D⁻¹ * (D * v * w) = u * (D⁻¹ * D) * (v * w) by ring, inv_mul_cancel₀ hD, mul_one]
  have hA' : ∀ φ : E n → ℂ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ {y : E n | (herm y).det ≠ 0} →
      ∫ x, φ (qX ε x) * (evX P x * gs c x) = ∫ β, φ β * g β := by
    intro φ hφc hφs hφU
    have hψc : Continuous (fun β : E n => φ β * (((Complex.I * (t : ℂ)) ^ n * (herm β).det) ^ N)⁻¹) := by
      apply continuous_of_tsupport
      intro β hβ
      have hβU : (herm β).det ≠ 0 := hφU (tsupport_mul_subset_left hβ)
      exact hφc.continuousAt.mul (hDc.continuousAt.inv₀ (pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hIt) hβU)))
    have hψs : HasCompactSupport (fun β : E n => φ β * (((Complex.I * (t : ℂ)) ^ n * (herm β).det) ^ N)⁻¹) := hφs.mul_right
    have key2 : (∫ x, (φ (qX ε x) * (((Complex.I * (t : ℂ)) ^ n * (herm (qX ε x)).det) ^ N)⁻¹) * (evX P' x * gs c x)) = ∫ β, (φ β * (((Complex.I * (t : ℂ)) ^ n * (herm β).det) ^ N)⁻¹) * ((((|t| / (2 * Real.pi)) ^ n ^ 2 : ℝ) : ℂ) * ∫ y : E n, FP ε c t P' y * Complex.exp (-(Complex.I * (t : ℂ) * (ip β y : ℂ)))) :=
      hM n (Fin m → Fin n → ℂ) volume (fun x => evX P' x * gs c x) (qX ε) (hI m n c hc P') hQc.measurable t ht0 hFP'int _ hψc hψs
    calc (∫ x, φ (qX ε x) * (evX P x * gs c x)) = ∫ x, (φ (qX ε x) * (((Complex.I * (t : ℂ)) ^ n * (herm (qX ε x)).det) ^ N)⁻¹) * (evX P' x * gs c x) := by
          congr 1
          funext x
          rw [hev x]
          by_cases h0 : φ (qX ε x) = 0
          · simp [h0]
          · have hne : (herm (qX ε x)).det ≠ 0 := hφU (subset_tsupport _ (Function.mem_support.mpr h0))
            rw [hHq x] at hne
            rw [hHq x]
            exact hcan _ _ _ _ (pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hIt) hne))
      _ = _ := key2
      _ = ∫ β, φ β * g β := by
          congr 1
          funext β
          rw [hg]
          ring
  refine ⟨g, hgU, ?_, ?_⟩
  · intro S hS hSU
    have hpre : gramX ε ⁻¹' (herm '' S) = qX ε ⁻¹' S := by
      ext x
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · rintro ⟨y, hy, hyx⟩
        have hyq : y = qX ε x := by
          calc y = hinv (herm y) := (hHinv y).symm
            _ = hinv (herm (qX ε x)) := by rw [hyx, hHq]
            _ = qX ε x := hHinv _
        rw [← hyq]
        exact hy
      · intro hx
        exact ⟨qX ε x, hx, hHq x⟩
    rw [hpre]
    have hUo : IsOpen {y : E n | (herm y).det ≠ 0} := isOpen_ne_fun hdc continuous_const
    obtain ⟨δ, hδ, hδU⟩ := hS.exists_cthickening_subset_open hUo hSU
    have hK : IsCompact (Metric.cthickening δ S) := hS.cthickening
    have hδk : ∀ k : ℕ, 0 < δ / ((k : ℝ) + 1) := fun k => div_pos hδ (Nat.cast_add_one_pos k)
    have hδt : Tendsto (fun k : ℕ => δ / ((k : ℝ) + 1)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul δ)
    have hle : ∀ k : ℕ, δ / ((k : ℝ) + 1) ≤ δ := fun k => div_le_self hδ.le (le_add_of_nonneg_left (Nat.cast_nonneg k))
    obtain ⟨φk, hφk⟩ : ∃ φk : ℕ → E n → ℂ, φk = fun k β => (((thickenedIndicator (hδk k) S β : NNReal) : ℝ) : ℂ) := ⟨_, rfl⟩
    have hφkc : ∀ k, Continuous (φk k) := by
      intro k
      rw [hφk]
      exact Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp (thickenedIndicator (hδk k) S).continuous)
    have hφk0 : ∀ k β, β ∉ Metric.cthickening δ S → φk k β = 0 := by
      intro k β hβ
      rw [hφk]
      simp only
      rw [thickenedIndicator_zero (hδk k) S (fun h => hβ (Metric.cthickening_mono (hle k) S (Metric.thickening_subset_cthickening _ _ h)))]
      simp
    have hφk1 : ∀ k β, ‖φk k β‖ ≤ 1 := by
      intro k β
      rw [hφk]
      simp only
      rw [Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _)]
      exact_mod_cast thickenedIndicator_le_one (hδk k) S β
    have hφks : ∀ k, HasCompactSupport (φk k) := fun k => HasCompactSupport.intro hK (hφk0 k)
    have hφkU : ∀ k, tsupport (φk k) ⊆ {y : E n | (herm y).det ≠ 0} := fun k =>
      (closure_minimal (Function.support_subset_iff'.2 (hφk0 k)) hK.isClosed).trans hδU
    have hlim : ∀ β : E n, Tendsto (fun k : ℕ => φk k β) atTop (𝓝 (S.indicator (fun _ => (1 : ℂ)) β)) := by
      intro β
      have h1 := tendsto_pi_nhds.1 (thickenedIndicator_tendsto_indicator_closure hδk hδt S) β
      rw [hS.isClosed.closure_eq] at h1
      have h2 := ((Complex.continuous_ofReal.comp NNReal.continuous_coe).tendsto _).comp h1
      rw [hφk]
      by_cases hβ : β ∈ S
      · simpa [hβ, Function.comp_def] using h2
      · simpa [hβ, Function.comp_def] using h2
    have hLt : Tendsto (fun k => ∫ x, φk k (qX ε x) * (evX P x * gs c x)) atTop (𝓝 (∫ x, S.indicator (fun _ => (1 : ℂ)) (qX ε x) * (evX P x * gs c x))) := by
      refine tendsto_integral_of_dominated_convergence (fun x => ‖evX P x * gs c x‖) (fun k => ?_) (hI m n c hc P).norm (fun k => Filter.Eventually.of_forall fun x => ?_) (Filter.Eventually.of_forall fun x => ?_)
      · exact ((hφkc k).comp hQc).aestronglyMeasurable.mul (hI m n c hc P).aestronglyMeasurable
      · rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hφk1 k _)
      · exact (hlim (qX ε x)).mul_const _
    have hgK : IntegrableOn g (Metric.cthickening δ S) volume := (hgU.mono hδU).integrableOn_compact hK
    have hRt : Tendsto (fun k => ∫ β, φk k β * g β) atTop (𝓝 (∫ β, S.indicator (fun _ => (1 : ℂ)) β * g β)) := by
      refine tendsto_integral_of_dominated_convergence ((Metric.cthickening δ S).indicator fun β => ‖g β‖) (fun k => ?_) (IntegrableOn.integrable_indicator hgK.norm hK.measurableSet) (fun k => Filter.Eventually.of_forall fun β => ?_) (Filter.Eventually.of_forall fun β => (hlim β).mul_const _)
      · exact (hφkc k).aestronglyMeasurable.mul hgm.aestronglyMeasurable
      · by_cases hβ : β ∈ Metric.cthickening δ S
        · rw [Set.indicator_of_mem hβ, norm_mul]
          exact mul_le_of_le_one_left (norm_nonneg _) (hφk1 k _)
        · simp [hβ, hφk0 k β hβ]
    have heq := tendsto_nhds_unique hLt (Filter.Tendsto.congr (fun k => (hA' (φk k) (hφkc k) (hφks k) (hφkU k)).symm) hRt)
    rw [← integral_indicator (hQc.measurable hS.isClosed.measurableSet), ← integral_indicator hS.isClosed.measurableSet]
    have e1 : ∀ x, (qX ε ⁻¹' S).indicator (fun x => evX P x * gs c x) x = S.indicator (fun _ => (1 : ℂ)) (qX ε x) * (evX P x * gs c x) := by
      intro x
      by_cases h : qX ε x ∈ S <;> simp [h]
    have e2 : ∀ β, S.indicator g β = S.indicator (fun _ => (1 : ℂ)) β * g β := by
      intro β
      by_cases h : β ∈ S <;> simp [h]
    simp only [e1, e2]
    exact heq
  · intro β _
    have hint : (∫ y : E n, Delta^[N] (fun y : E n => secN ε c t P (herm y)) y * chr t β y) = ∫ y : E n, FP ε c t P' y * Complex.exp (-(Complex.I * (t : ℂ) * (ip β y : ℂ))) := by
      have hfun : (fun y : E n => secN ε c t P (herm y)) = FP ε c t P := funext (hsec P)
      rw [hfun, hDP']
      rfl
    rw [hint, hg]
    have h1 : ((-1 : ℂ) ^ n / (-(Complex.I * (t : ℂ))) ^ n) = ((Complex.I * (t : ℂ)) ^ n)⁻¹ := by
      rw [neg_pow (Complex.I * (t : ℂ)), div_mul_eq_div_div, div_self (pow_ne_zero _ (by norm_num)), one_div]
    rw [h1]
    have hab : (((2 * Real.pi / |t|) ^ n ^ 2 : ℝ) : ℂ) * (((|t| / (2 * Real.pi)) ^ n ^ 2 : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, ← mul_pow, div_mul_div_comm, mul_comm (2 * Real.pi) |t|, div_self (mul_ne_zero (abs_ne_zero.mpr ht0) (by positivity)), one_pow, Complex.ofReal_one]
    linear_combination (((herm β).det ^ N)⁻¹ * (((Complex.I * (t : ℂ)) ^ n)⁻¹) ^ N * ∫ y : E n, FP ε c t P' y * Complex.exp (-(Complex.I * (t : ℂ) * (ip β y : ℂ)))) * hab

end PositivityTheory.Rg.Sw.WR.D
end
end

namespace PositivityTheory.Rg.Sw.WR.D

theorem densOf3 : Gauss → ClsGain → Integr → Dens := dens_of algA intG derivF mollId

end PositivityTheory.Rg.Sw.WR.D
