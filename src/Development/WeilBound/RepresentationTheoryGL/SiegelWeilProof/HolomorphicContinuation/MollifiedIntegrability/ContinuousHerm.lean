module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ClsBoundAlt

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.DifferentiableOfTop
noncomputable section

open MeasureTheory Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.WR.T

open PositivityTheory.Rg.Sw

variable {n : ℕ}

def FD (L : List (Fin n × Fin n)) (f : E n → ℂ) : E n → ℂ := L.foldr (fun kl g => Dkl kl.1 kl.2 g) f

theorem FD_cons (kl : Fin n × Fin n) (L : List (Fin n × Fin n)) (f : E n → ℂ) :
    FD (kl :: L) f = Dkl kl.1 kl.2 (FD L f) := rfl

theorem FD_append (L L' : List (Fin n × Fin n)) (f : E n → ℂ) : FD (L ++ L') f = FD L (FD L' f) := by
  simp [FD, List.foldr_append]

theorem contDiff_dirC {f : E n → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (w : Fin n → Fin n → ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (dirC f w) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) := (contDiff_infty_iff_fderiv.1 hf).2
  have ha : ContDiff ℝ (⊤ : ℕ∞) (fun y => fderiv ℝ f y (fun a b => (w a b).re)) := h1.clm_apply contDiff_const
  have hb : ContDiff ℝ (⊤ : ℕ∞) (fun y => fderiv ℝ f y (fun a b => (w a b).im)) := h1.clm_apply contDiff_const
  exact ha.add (contDiff_const.mul hb)

theorem contDiff_Dkl {f : E n → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (k l : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (Dkl k l f) := contDiff_dirC hf _

theorem contDiff_FD {f : E n → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (L : List (Fin n × Fin n)) :
    ContDiff ℝ (⊤ : ℕ∞) (FD L f) := by
  induction L with
  | nil => exact hf
  | cons kl L ih => exact contDiff_Dkl ih _ _

theorem differentiable_of_top {f : E n → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) : Differentiable ℝ f :=
  hf.differentiable (by simp)

theorem Dkl_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (F : ι → E n → ℂ) (hF : ∀ i ∈ s, Differentiable ℝ (F i))
    (k l : Fin n) : Dkl k l (fun y => ∑ i ∈ s, c i * F i y) = fun y => ∑ i ∈ s, c i * Dkl k l (F i) y := by
  funext y
  unfold Dkl dirC
  have hfun : (fun y => ∑ i ∈ s, c i * F i y) = ∑ i ∈ s, (fun y => c i * F i y) := by
    funext y; simp [Finset.sum_apply]
  rw [hfun, fderiv_sum (fun i hi => ((hF i hi) y).const_mul (c i))]
  have e : ∀ i ∈ s, fderiv ℝ (fun y => c i * F i y) y = c i • fderiv ℝ (F i) y :=
    fun i hi => fderiv_const_mul ((hF i hi) y) (c i)
  rw [Finset.sum_congr rfl e]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => by ring

theorem FD_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (F : ι → E n → ℂ) (hF : ∀ i ∈ s, ContDiff ℝ (⊤ : ℕ∞) (F i))
    (L : List (Fin n × Fin n)) : FD L (fun y => ∑ i ∈ s, c i * F i y) = fun y => ∑ i ∈ s, c i * FD L (F i) y := by
  induction L with
  | nil => rfl
  | cons kl L ih =>
    rw [FD_cons, ih]
    exact Dkl_sum s c (fun i => FD L (F i)) (fun i hi => differentiable_of_top (contDiff_FD (hF i hi) L)) _ _

def Ls (σ : Equiv.Perm (Fin n)) : List (Fin n × Fin n) := (List.finRange n).map fun k => (k, σ k)

theorem Delta_eq (f : E n → ℂ) :
    Delta f = fun y => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * FD (Ls σ) f y := by
  funext y
  simp only [Delta, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, FD, Ls, List.foldr_map]

def Good (f : E n → ℂ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) f ∧ ∀ L : List (Fin n × Fin n), ∃ h : E n → ℝ, Integrable h ∧ ∀ y, ‖FD L f y‖ ≤ h y

theorem good_FD {f : E n → ℂ} (hf : Good f) (L : List (Fin n × Fin n)) : Good (FD L f) := by
  refine ⟨contDiff_FD hf.1 L, fun L' => ?_⟩
  rw [← FD_append]
  exact hf.2 _

theorem good_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (F : ι → E n → ℂ) (hF : ∀ i ∈ s, Good (F i)) :
    Good (fun y => ∑ i ∈ s, c i * F i y) := by
  refine ⟨?_, fun L => ?_⟩
  · exact ContDiff.sum fun i hi => contDiff_const.mul (hF i hi).1
  · rw [FD_sum s c F (fun i hi => (hF i hi).1) L]
    have : ∀ i ∈ s, ∃ h : E n → ℝ, Integrable h ∧ ∀ y, ‖FD L (F i) y‖ ≤ h y := fun i hi => (hF i hi).2 L
    choose! h hint hb using this
    refine ⟨fun y => ∑ i ∈ s, ‖c i‖ * h i y, MeasureTheory.integrable_finsetSum s fun i hi => (hint i hi).const_mul _, fun y => ?_⟩
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hb i hi y) (norm_nonneg _)

theorem good_Delta {f : E n → ℂ} (hf : Good f) : Good (Delta f) := by
  rw [Delta_eq]
  exact good_sum _ _ _ fun σ _ => good_FD hf _

theorem good_iter {f : E n → ℂ} (hf : Good f) (k : ℕ) : Good (Delta^[k] f) := by
  induction k with
  | zero => exact hf
  | succ k ih => rw [Function.iterate_succ_apply']; exact good_Delta ih

theorem ibp_iter (hIBP : IBP) {f : E n → ℂ} (hf : Good f) (t : ℝ) (β : E n) (ht : t ≠ 0) (hβ : (herm β).det ≠ 0)
    (N : ℕ) : ∫ y, f y * chr t β y =
      ((-1) ^ n * ((-(Complex.I * t)) ^ n * (herm β).det)⁻¹) ^ N * ∫ y, (Delta^[N] f) y * chr t β y := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [ih, hIBP n (Delta^[N] f) t β (good_iter hf N).1 ht hβ (good_iter hf N).2, Function.iterate_succ_apply', pow_succ]
    ring

end PositivityTheory.Rg.Sw.WR.T
end
end

noncomputable section

open MeasureTheory Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.WR.T

open PositivityTheory.Rg.Sw

variable {n : ℕ}

theorem continuous_herm : Continuous (herm : E n → Matrix (Fin n) (Fin n) ℂ) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  unfold herm
  fun_prop

theorem continuous_dP : Continuous (dP : E n → ℝ) := by
  unfold dP
  exact Complex.continuous_re.comp ((continuous_const.add (continuous_herm.matrix_mul continuous_herm)).matrix_det)

theorem continuous_chr (t : ℝ) (β : E n) : Continuous (chr t β) := by
  unfold chr
  fun_prop

theorem norm_chr (t : ℝ) (β y : E n) : ‖chr t β y‖ = 1 := by
  unfold chr
  rw [Complex.norm_exp]
  simp

theorem abs_log_le (x δ : ℝ) (hx : 0 < x) (hδ : 0 < δ) : |Real.log x| ≤ (x ^ δ + x ^ (-δ)) / δ := by
  have h1 : δ * Real.log x ≤ x ^ δ := by
    rw [← Real.log_rpow hx]
    have := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx δ)
    linarith
  have h2 : -δ * Real.log x ≤ x ^ (-δ) := by
    rw [← Real.log_rpow hx]
    have := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx (-δ))
    linarith
  have p1 := Real.rpow_pos_of_pos hx δ
  have p2 := Real.rpow_pos_of_pos hx (-δ)
  rcases abs_cases (Real.log x) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h, le_div_iff₀ hδ] <;> nlinarith

theorem rpow_neg_le_add (x a a0 d : ℝ) (hx : 0 < x) (ha : |a - a0| ≤ d) :
    x ^ (-a) ≤ x ^ (-(a0 - d)) + x ^ (-(a0 + d)) := by
  obtain ⟨ha1, ha2⟩ := abs_le.1 ha
  have p1 := Real.rpow_pos_of_pos hx (-(a0 - d))
  have p2 := Real.rpow_pos_of_pos hx (-(a0 + d))
  rcases le_or_gt 1 x with h1 | h1
  · have : x ^ (-a) ≤ x ^ (-(a0 - d)) := Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
    linarith
  · have : x ^ (-a) ≤ x ^ (-(a0 + d)) := Real.rpow_le_rpow_of_exponent_ge hx h1.le (by linarith)
    linarith

theorem rp3 {x : ℝ} (hx : 0 < x) (a b c : ℝ) : x ^ a * x ^ b * x ^ c = x ^ (a + b + c) := by
  rw [Real.rpow_add hx, Real.rpow_add hx]

theorem dP_pos (hI : Integr) (y : E n) : 0 < dP y := by
  obtain ⟨⟨c0, hc0, hc0le⟩, -⟩ := hI n
  exact lt_of_lt_of_le (mul_pos hc0 (by positivity)) (hc0le y)

theorem norm_term (hI : Integr) (t : ℝ) (β : E n) (h : E n → ℂ) (z : ℂ) (y : E n) :
    ‖((dP y : ℝ) : ℂ) ^ (-z) * h y * chr t β y‖ = dP y ^ (-z.re) * ‖h y‖ := by
  rw [norm_mul, norm_mul, norm_chr, mul_one, Complex.norm_cpow_eq_rpow_re_of_pos (dP_pos hI y), Complex.neg_re]

theorem continuous_term (hI : Integr) (t : ℝ) (β : E n) {h : E n → ℂ} (hh : Continuous h) (z : ℂ) :
    Continuous fun y => ((dP y : ℝ) : ℂ) ^ (-z) * h y * chr t β y := by
  have hslit : ∀ y : E n, ((dP y : ℝ) : ℂ) ∈ Complex.slitPlane := fun y => Complex.ofReal_mem_slitPlane.2 (dP_pos hI y)
  have : Continuous fun y => ((dP y : ℝ) : ℂ) ^ (-z) :=
    (Complex.continuous_ofReal.comp continuous_dP).cpow continuous_const hslit
  exact (this.mul hh).mul (continuous_chr t β)

theorem integ_term (hI : Integr) (t : ℝ) (β : E n) {h : E n → ℂ} (hh : Continuous h) {κ C : ℝ}
    (hb : ∀ y, ‖h y‖ ≤ C * dP y ^ (-κ)) {z : ℂ} (hz : (n : ℝ) ^ 2 / 2 < z.re + κ) :
    Integrable fun y => ((dP y : ℝ) : ℂ) ^ (-z) * h y * chr t β y := by
  obtain ⟨-, hint⟩ := hI n
  refine Integrable.mono' ((hint (z.re + κ) hz).const_mul C) (continuous_term hI t β hh z).aestronglyMeasurable
    (ae_of_all _ fun y => ?_)
  rw [norm_term hI]
  have hp := dP_pos hI y
  calc dP y ^ (-z.re) * ‖h y‖ ≤ dP y ^ (-z.re) * (C * dP y ^ (-κ)) :=
        mul_le_mul_of_nonneg_left (hb y) (Real.rpow_nonneg hp.le _)
    _ = C * dP y ^ (-(z.re + κ)) := by
        rw [neg_add, Real.rpow_add hp]; ring

theorem holo (hI : Integr) (t : ℝ) (β : E n) {h : E n → ℂ} (hh : Continuous h) (κ C : ℝ)
    (hb : ∀ y, ‖h y‖ ≤ C * dP y ^ (-κ)) :
    DifferentiableOn ℂ (fun z : ℂ => ∫ y, ((dP y : ℝ) : ℂ) ^ (-z) * h y * chr t β y)
      {z : ℂ | (n : ℝ) ^ 2 / 2 < z.re + κ} := by
  obtain ⟨-, hint⟩ := hI n
  intro z0 hz0
  simp only [Set.mem_ofPred_eq] at hz0
  set σs := z0.re + κ with hσs
  set δ := (σs - (n : ℝ) ^ 2 / 2) / 4 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hb' : ∀ y, ‖h y‖ ≤ C' * dP y ^ (-κ) := fun y =>
    (hb y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (dP_pos hI y).le _))
  let F : ℂ → E n → ℂ := fun z y => ((dP y : ℝ) : ℂ) ^ (-z) * h y * chr t β y
  let F' : ℂ → E n → ℂ := fun z y => ((dP y : ℝ) : ℂ) ^ (-z) * (-((Real.log (dP y) : ℝ) : ℂ)) * h y * chr t β y
  have hF'c : Continuous (F' z0) := by
    have hslit : ∀ y : E n, ((dP y : ℝ) : ℂ) ∈ Complex.slitPlane := fun y => Complex.ofReal_mem_slitPlane.2 (dP_pos hI y)
    have h1 : Continuous fun y => ((dP y : ℝ) : ℂ) ^ (-z0) :=
      (Complex.continuous_ofReal.comp continuous_dP).cpow continuous_const hslit
    have h2 : Continuous fun y : E n => ((Real.log (dP y) : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (continuous_dP.log fun y => (dP_pos hI y).ne')
    exact ((h1.mul h2.neg).mul hh).mul (continuous_chr t β)
  let B : E n → ℝ := fun y => C' / δ * 2 * (dP y ^ (-(σs - 2 * δ)) + dP y ^ (-(σs + 2 * δ)))
  have hBint : Integrable B := by
    refine ((hint _ ?_).add (hint _ ?_)).const_mul (C' / δ * 2)
    · rw [hδ]; linarith
    · rw [hδ]; linarith
  have hbound : ∀ y, ∀ z ∈ Metric.ball z0 δ, ‖F' z y‖ ≤ B y := by
    intro y z hz
    have hp := dP_pos hI y
    have hre : |z.re - z0.re| < δ := by
      have := Complex.abs_re_le_norm (z - z0)
      rw [Complex.sub_re] at this
      exact lt_of_le_of_lt this (by simpa [dist_eq_norm] using hz)
    have hn : ‖F' z y‖ = dP y ^ (-z.re) * |Real.log (dP y)| * ‖h y‖ := by
      simp only [F', norm_mul, norm_neg, norm_chr, mul_one, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_cpow_eq_rpow_re_of_pos hp, Complex.neg_re]
    rw [hn]
    have e1 := abs_log_le (dP y) δ hp hδpos
    have e2 := hb' y
    have q1 : dP y ^ δ * dP y ^ (-z.re) * dP y ^ (-κ) = dP y ^ (-(z.re + κ - δ)) := by
      rw [rp3 hp]; congr 1; ring
    have q2 : dP y ^ (-δ) * dP y ^ (-z.re) * dP y ^ (-κ) = dP y ^ (-(z.re + κ + δ)) := by
      rw [rp3 hp]; congr 1; ring
    have r1 := rpow_neg_le_add (dP y) (z.re + κ - δ) σs (2 * δ) hp (by rw [abs_le]; constructor <;>
      linarith [(abs_lt.1 hre).1, (abs_lt.1 hre).2])
    have r2 := rpow_neg_le_add (dP y) (z.re + κ + δ) σs (2 * δ) hp (by rw [abs_le]; constructor <;>
      linarith [(abs_lt.1 hre).1, (abs_lt.1 hre).2])
    have a0 := Real.rpow_nonneg hp.le (-z.re)
    have a1 := Real.rpow_nonneg hp.le δ
    have a2 := Real.rpow_nonneg hp.le (-δ)
    have a3 := Real.rpow_nonneg hp.le (-κ)
    calc dP y ^ (-z.re) * |Real.log (dP y)| * ‖h y‖
        ≤ dP y ^ (-z.re) * ((dP y ^ δ + dP y ^ (-δ)) / δ) * (C' * dP y ^ (-κ)) := by
          gcongr
      _ = C' / δ * (dP y ^ δ * dP y ^ (-z.re) * dP y ^ (-κ) + dP y ^ (-δ) * dP y ^ (-z.re) * dP y ^ (-κ)) := by
          ring
      _ = C' / δ * (dP y ^ (-(z.re + κ - δ)) + dP y ^ (-(z.re + κ + δ))) := by rw [q1, q2]
      _ ≤ B y := by
          have : 0 ≤ C' / δ := div_nonneg hC'0 hδpos.le
          simp only [B]
          nlinarith
  have hdiff : ∀ y, ∀ z ∈ Metric.ball z0 δ, HasDerivAt (fun w => F w y) (F' z y) z := by
    intro y z _
    have hp := dP_pos hI y
    have hx : ((dP y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
    have h1 : HasDerivAt (fun w : ℂ => ((dP y : ℝ) : ℂ) ^ (-w))
        (((dP y : ℝ) : ℂ) ^ (-z) * Complex.log ((dP y : ℝ) : ℂ) * (-1)) z :=
      ((Complex.hasStrictDerivAt_const_cpow (Or.inl hx)).hasDerivAt).comp z (hasDerivAt_neg z)
    have h2 := (h1.mul_const (h y)).mul_const (chr t β y)
    refine h2.congr_deriv ?_
    show _ = ((dP y : ℝ) : ℂ) ^ (-z) * (-((Real.log (dP y) : ℝ) : ℂ)) * h y * chr t β y
    rw [Complex.ofReal_log hp.le]
    ring
  have hF0 : Integrable (F z0) := integ_term hI t β hh hb' hz0
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := F) (x₀ := z0)
    (Metric.ball_mem_nhds z0 hδpos)
    (Eventually.of_forall fun z => (continuous_term hI t β hh z).aestronglyMeasurable) hF0
    hF'c.aestronglyMeasurable (ae_of_all _ hbound) hBint (ae_of_all _ hdiff)
  exact key.2.differentiableAt.differentiableWithinAt

end PositivityTheory.Rg.Sw.WR.T
