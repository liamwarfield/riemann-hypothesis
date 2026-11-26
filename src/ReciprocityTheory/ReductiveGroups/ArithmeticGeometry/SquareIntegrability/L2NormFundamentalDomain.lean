module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.LemmaS
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtData
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.DimStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PropAA

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.L2NormFundamentalDomain
namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex

noncomputable section

theorem contDiff_of_diff {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    {f : W → ℂ} (hf : Differentiable ℂ f) : ContDiff ℂ (⊤ : ℕ∞) f := by
  let e := (Module.finBasis ℂ W).equivFun.toContinuousLinearEquiv
  have h1 : Differentiable ℂ (f ∘ e.symm) := by
    first
    | exact hf.comp e.symm.differentiable
    | exact hf.comp (e.symm.contDiff.differentiable (by simp))
  have h3 := (contDiff_of_differentiable h1 (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).comp e.contDiff
  convert h3 using 1
  funext v; simp

theorem jof_Hf_self_re {ι : Type} [Fintype ι] (x : EuclideanSpace ℂ ι) : (Hf x x).re = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq x, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp [Hf, Complex.re_sum, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  refine Finset.sum_congr rfl fun i _ => ?_
  first
  | rw [← Complex.ofReal_pow, Complex.ofReal_re]
  | norm_cast
  | simp [sq]

variable {E : Type} [Field E] [NumberField E] (X : PT E)

def tens {n : ℕ} (s : Fin n → (Fin 1 → Vsp X.dim) → ℂ) : (Fin n → Vsp X.dim) → ℂ :=
  fun v => ∏ k, s k (fun _ => v k)

theorem sec_contDiff {q n : ℕ} {F : (Fin n → Vsp X.dim) → ℂ} (hF : F ∈ X.Sec q n) :
    ContDiff ℂ (⊤ : ℕ∞) F := by
  exact contDiff_of_diff (show Differentiable ℂ F ∧ _ from hF).1

theorem tens_mem {n q : ℕ} {s : Fin n → (Fin 1 → Vsp X.dim) → ℂ} (hs : ∀ k, s k ∈ X.Sec q 1) :
    tens X s ∈ X.Sec q n := by
  have hd : ∀ k, Differentiable ℂ (s k) := fun k => (show Differentiable ℂ (s k) ∧ _ from hs k).1
  show _ ∧ _
  refine ⟨?_, fun γ hγ v => ?_⟩
  · show Differentiable ℂ (fun v : Fin n → Vsp X.dim => ∏ k, s k (fun _ => v k))
    first
    | exact Differentiable.finset_prod (fun k _ => (hd k).comp (differentiable_pi.mpr fun _ => differentiable_apply k))
    | fun_prop
  · have he : ∀ k, s k (fun _ => (v + γ) k) = ((X.eps (γ k) : ℂ)) ^ q *
        cexp (q * Real.pi * Hf (v k) (γ k) + q * Real.pi * Hf (γ k) (γ k) / 2) * s k (fun _ => v k) := by
      intro k
      have := (show Differentiable ℂ (s k) ∧ ∀ γ' : Fin 1 → Vsp X.dim, (∀ j, γ' j ∈ X.L) →
        ∀ w, s k (w + γ') = (∏ j, (X.eps (γ' j) : ℂ)) ^ q *
          cexp (q * Real.pi * HC w γ' + q * Real.pi * HC γ' γ' / 2) * s k w from hs k).2
        (fun _ => γ k) (fun _ => hγ k) (fun _ => v k)
      simpa [HC, Pi.add_def] using this
    have hsum : ∑ k, ((q : ℂ) * Real.pi * Hf (v k) (γ k) + q * Real.pi * Hf (γ k) (γ k) / 2) =
        q * Real.pi * HC v γ + q * Real.pi * HC γ γ / 2 := by
      simp only [HC, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_div]
    show ∏ k, s k (fun _ => (v + γ) k) = (∏ k, (X.eps (γ k) : ℂ)) ^ q *
      cexp (q * Real.pi * HC v γ + q * Real.pi * HC γ γ / 2) * ∏ k, s k (fun _ => v k)
    rw [Finset.prod_congr rfl fun k _ => he k, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_pow, ← Complex.exp_sum, hsum]

theorem pointNormSq_tensor {n : ℕ} (q : ℕ) (s : Fin n → (Fin 1 → Vsp X.dim) → ℂ) (v : Fin n → Vsp X.dim) :
    X.ptN2 q (tens X s) v = ∏ k, X.ptN2 q (s k) (fun _ => v k) := by
  have hHC : (HC v v).re = ∑ k, (HC (fun _ : Fin 1 => v k) (fun _ => v k)).re := by
    simp [HC, Complex.re_sum]
  simp only [PT.ptN2, tens]
  rw [norm_prod, ← Finset.prod_pow, hHC, Finset.mul_sum, Real.exp_sum, ← Finset.prod_mul_distrib]

theorem avg_fd_prod {n : ℕ} (f : Fin n → Vsp X.dim → ℝ) :
    ⨍ v in X.fd n, ∏ k, f k (v k) = ∏ k, ⨍ x in ZSpan.fundamentalDomain X.b, f k x := by
  have hfd : X.fd n = Set.univ.pi (fun _ : Fin n => ZSpan.fundamentalDomain X.b) := by
    ext v; simp [PT.fd]
  rw [hfd]
  simp only [MeasureTheory.setAverage_eq, smul_eq_mul]
  rw [MeasureTheory.volume_pi, MeasureTheory.Measure.restrict_pi_pi]
  simp only [MeasureTheory.measureReal_def]
  rw [MeasureTheory.Measure.pi_pi, ENNReal.toReal_prod, ← Finset.prod_inv_distrib]
  first
  | rw [MeasureTheory.integral_fintype_prod_eq_prod, ← Finset.prod_mul_distrib]
  | rw [MeasureTheory.integral_fintype_prod_eq_prod (μ := fun _ => _), ← Finset.prod_mul_distrib]

theorem l2_norm_fundamental_domain (q : ℕ) (s : (Fin 1 → Vsp X.dim) → ℂ) :
    X.l2 q s = ⨍ x in ZSpan.fundamentalDomain X.b, X.ptN2 q s (fun _ => x) := by
  have hv : ∀ v : Fin 1 → Vsp X.dim, (fun _ : Fin 1 => v 0) = v :=
    fun v => funext fun k => by rw [Subsingleton.elim k 0]
  have h := avg_fd_prod X (n := 1) (fun _ x => X.ptN2 q s (fun _ => x))
  simp only [Fin.prod_univ_one, hv] at h
  exact h

theorem l2_tens_eq_prod {n : ℕ} (q : ℕ) (s : Fin n → (Fin 1 → Vsp X.dim) → ℂ) :
    X.l2 q (tens X s) = ∏ k, X.l2 q (s k) := by
  rw [Finset.prod_congr rfl fun k _ => l2_norm_fundamental_domain X q (s k)]
  rw [PT.l2]
  simp_rw [pointNormSq_tensor X q s]
  exact avg_fd_prod X (fun k x => X.ptN2 q (s k) (fun _ => x))

theorem l2_smul {n : ℕ} (q : ℕ) (c : ℂ) (F : (Fin n → Vsp X.dim) → ℂ) :
    X.l2 q (c • F) = ‖c‖ ^ 2 * X.l2 q F := by
  have h : ∀ v, X.ptN2 q (c • F) v = ‖c‖ ^ 2 * X.ptN2 q F v := by
    intro v
    simp only [PT.ptN2, Pi.smul_apply, smul_eq_mul, norm_mul]
    ring
  simp only [PT.l2, h]
  first
  | exact MeasureTheory.integral_const_mul _ _
  | exact MeasureTheory.integral_mul_left _ _
  | simp [MeasureTheory.average, MeasureTheory.integral_const_mul]

def gtOf (q : ℕ) : GT (Idx X.dim) where
  b := X.b
  integral := X.integral
  perfect := X.perfect
  ka := fun γ => (X.eps γ : ℂ) ^ q
  ka_abs := fun x hx => by rcases X.eps_pm x hx with h | h <;> simp [h]

theorem eq_zero_of_l2_eq_zero (hP : Ext.PackingCount) {q : ℕ} (hq : 1 ≤ q) {s : (Fin 1 → Vsp X.dim) → ℂ}
    (hs : s ∈ X.Sec q 1) (h0 : X.l2 q s = 0) : s = 0 := by
  have hd : Differentiable ℂ s := (show Differentiable ℂ s ∧ _ from hs).1
  set g : Vsp X.dim → ℂ := fun z => s (fun _ => z) with hgdef
  have hgc : Continuous g := (hd.comp (differentiable_pi.mpr fun _ => differentiable_id)).continuous
  have hq' : ∀ γ ∈ X.L, ∀ x, g (x + γ) = ((X.eps γ : ℂ)) ^ q *
      cexp (q * Real.pi * Hf x γ + q * Real.pi * Hf γ γ / 2) * g x := by
    intro γ hγ x
    have := (show Differentiable ℂ s ∧ ∀ γ' : Fin 1 → Vsp X.dim, (∀ j, γ' j ∈ X.L) →
        ∀ w, s (w + γ') = (∏ j, (X.eps (γ' j) : ℂ)) ^ q *
          cexp (q * Real.pi * HC w γ' + q * Real.pi * HC γ' γ' / 2) * s w from hs).2
      (fun _ => γ) (fun _ => hγ) (fun _ => x)
    simpa [HC, Pi.add_def, hgdef] using this
  have hne : ∀ γ ∈ X.L, ∀ x, g (x + γ) = 0 ↔ g x = 0 := by
    intro γ hγ x
    rw [hq' γ hγ x]
    have h1 : (X.eps γ : ℂ) ≠ 0 := by rcases X.eps_pm γ hγ with h | h <;> simp [h]
    simp [h1, Complex.exp_ne_zero]
  have hpx : ∀ x, X.ptN2 q s (fun _ => x) = ‖g x‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖x‖ ^ 2) := by
    intro x
    have hre : (HC (fun _ : Fin 1 => x) (fun _ => x)).re = ‖x‖ ^ 2 := by simp [HC, jof_Hf_self_re]
    simp only [PT.ptN2, hre, hgdef]
  have hl := l2_norm_fundamental_domain X q s
  rw [h0] at hl
  simp only [hpx] at hl
  set D := ZSpan.fundamentalDomain X.b with hD
  have hDm : MeasurableSet D := ZSpan.fundamentalDomain_measurableSet X.b
  have hDb : Bornology.IsBounded D := ZSpan.fundamentalDomain_isBounded X.b
  haveI : MeasureTheory.VAddInvariantMeasure (Submodule.span ℤ (Set.range X.b)) (Vsp X.dim)
      MeasureTheory.volume :=
    ⟨fun c s _ => by
      simpa [Submodule.vadd_def, vadd_eq_add] using
        MeasureTheory.measure_preimage_add MeasureTheory.volume (c : Vsp X.dim) s⟩
  have hfd := ZSpan.isAddFundamentalDomain X.b (MeasureTheory.volume : MeasureTheory.Measure (Vsp X.dim))
  have hD0 : MeasureTheory.volume D ≠ 0 := hfd.measure_ne_zero (NeZero.ne _)
  have hDt : MeasureTheory.volume D ≠ ⊤ := hDb.measure_lt_top.ne
  have hcont : Continuous fun x : Vsp X.dim => ‖g x‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖x‖ ^ 2) := by
    first
    | fun_prop
    | exact ((continuous_norm.comp hgc).pow 2).mul
        (Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2)))
  have hint : MeasureTheory.IntegrableOn
      (fun x : Vsp X.dim => ‖g x‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖x‖ ^ 2)) D :=
    (hcont.continuousOn.integrableOn_compact hDb.isCompact_closure).mono_set subset_closure
  rw [MeasureTheory.setAverage_eq, smul_eq_mul] at hl
  have hI : ∫ x in D, ‖g x‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖x‖ ^ 2) = 0 := by
    have hr : MeasureTheory.volume.real D ≠ 0 := by
      rw [MeasureTheory.measureReal_def]
      exact ENNReal.toReal_ne_zero.mpr ⟨hD0, hDt⟩
    rcases mul_eq_zero.mp hl.symm with h | h
    · exact absurd (inv_eq_zero.mp h) hr
    · exact h
  have hae := (MeasureTheory.setIntegral_eq_zero_iff_of_nonneg_ae
    (MeasureTheory.ae_of_all _ fun x => by show (0:ℝ) ≤ _; positivity) hint).mp hI
  have h2 : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (Vsp X.dim)), x ∈ D → g x = 0 := by
    rw [← MeasureTheory.ae_restrict_iff' hDm]
    filter_upwards [hae] with x hx
    simpa [Real.exp_ne_zero] using hx
  rw [MeasureTheory.ae_iff] at h2
  have hset : {x | ¬(x ∈ D → g x = 0)} = {x | g x ≠ 0} ∩ D := by
    ext x; simp [and_comm]
  rw [hset] at h2
  open Pointwise in
  have hinv : ∀ γ : Submodule.span ℤ (Set.range X.b), γ +ᵥ {x | g x ≠ 0} = {x | g x ≠ 0} := by
    intro γ
    ext y
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simp only [Set.mem_setOf_eq]
    have e : (-γ) +ᵥ y = y + -(γ : Vsp X.dim) := by
      first
      | (rw [Submodule.vadd_def, add_comm]; rfl)
      | simp [Submodule.vadd_def, add_comm]
      | (show ((-γ : Submodule.span ℤ (Set.range X.b)) : Vsp X.dim) + y = _; simp [add_comm])
    rw [e]
    exact not_congr (hne _ (neg_mem γ.2) y)
  have ht0 := hfd.measure_zero_of_invariant {x | g x ≠ 0} hinv h2
  have hopen : IsOpen {x | g x ≠ 0} := isOpen_ne_fun hgc continuous_const
  have hempty : {x | g x ≠ 0} = ∅ := (hopen.measure_eq_zero_iff MeasureTheory.volume).mp ht0
  funext v
  show s v = 0
  have hv : v = fun _ => v 0 := funext fun k => by rw [Subsingleton.elim k 0]
  have hz : g (v 0) = 0 := by
    by_contra hc
    have hm : v 0 ∈ ({x | g x ≠ 0} : Set (Vsp X.dim)) := hc
    rw [hempty] at hm
    exact hm
  rw [hv]
  exact hz

theorem polyDeriv_zero_fun {σ W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    (P : MvPolynomial σ ℂ) (u : σ → W) (x : W) : polyDeriv P u (0 : W → ℂ) x = 0 := by
  simp [polyDeriv, Pi.zero_def]

theorem polyDeriv_smul_fun {σ W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    (P : MvPolynomial σ ℂ) (u : σ → W) {F : W → ℂ} (hF : ContDiff ℂ (⊤ : ℕ∞) F) (c : ℂ) (x : W) :
    polyDeriv P u (c • F) x = c * polyDeriv P u F x := by
  unfold polyDeriv
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  first
  | rw [iteratedFDeriv_const_smul_apply ((hF.of_le (by exact_mod_cast le_top)).contDiffAt)]
  | rw [iteratedFDeriv_const_smul_apply (hF.of_le (by exact_mod_cast le_top))]
  simp only [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  ring

end

end ReciprocityTheory.ChartRestriction.G.I2
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ActEMemSpanOmega
namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex
open scoped InnerProductSpace

noncomputable section

variable {E : Type} [Field E] [NumberField E]

section act

variable {dim : (E →+* ℂ) → ℕ}

def actE (β : E) (v : Vsp dim) : Vsp dim := WithLp.toLp 2 fun i => i.1 β * v i

theorem act_eq_actE (α : 𝓞 E) (v : Vsp dim) : act α v = actE (α : E) v := rfl

@[simp] theorem actE_apply (β : E) (v : Vsp dim) (i : Idx dim) : actE β v i = i.1 β * v i := rfl

theorem actE_add_right (β : E) (v w : Vsp dim) : actE β (v + w) = actE β v + actE β w := by
  ext i
  simp [mul_add]

theorem actE_smul_right (β : E) (c : ℂ) (v : Vsp dim) : actE β (c • v) = c • actE β v := by
  ext i
  simp only [actE_apply, PiLp.smul_apply, smul_eq_mul]
  ring

theorem actE_rsmul_right (β : E) (r : ℝ) (v : Vsp dim) : actE β (r • v) = r • actE β v := by
  ext i
  simp only [actE_apply, PiLp.smul_apply, Complex.real_smul]
  ring

theorem actE_zero_right (β : E) : actE β (0 : Vsp dim) = 0 := by
  ext i
  simp

theorem actE_add_left (β γ : E) (v : Vsp dim) : actE (β + γ) v = actE β v + actE γ v := by
  ext i
  simp [add_mul]

theorem actE_zero_left (v : Vsp dim) : actE (0 : E) v = 0 := by
  ext i
  simp

theorem actE_one (v : Vsp dim) : actE (1 : E) v = v := by
  ext i
  simp

theorem actE_mul (β γ : E) (v : Vsp dim) : actE (β * γ) v = actE β (actE γ v) := by
  ext i
  simp [mul_assoc]

theorem actE_qsmul (q : ℚ) (β : E) (v : Vsp dim) : actE (q • β) v = (q : ℝ) • actE β v := by
  ext i
  simp only [actE_apply, PiLp.smul_apply, Complex.real_smul, Rat.smul_def, map_mul, map_ratCast,
    Complex.ofReal_ratCast]
  ring

theorem act_one' (v : Vsp dim) : act (1 : 𝓞 E) v = v := by
  rw [act_eq_actE]
  simpa using actE_one v

theorem act_mul' (α β : 𝓞 E) (v : Vsp dim) : act (α * β) v = act α (act β v) := by
  rw [act_eq_actE, act_eq_actE, act_eq_actE]
  push_cast
  exact actE_mul _ _ v

theorem norm_actE_le (β : E) (Ω : ℝ) (hΩ : 0 ≤ Ω) (h : ∀ σ : E →+* ℂ, ‖σ β‖ ≤ Ω) (v : Vsp dim) :
    ‖actE β v‖ ≤ Ω * ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, ← Real.sqrt_sq hΩ, ← Real.sqrt_mul (sq_nonneg _)]
  apply Real.sqrt_le_sqrt
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [actE_apply, norm_mul, mul_pow]
  gcongr
  exact h i.1

theorem actE_mem_of_span (β : E) (S : Set (Vsp dim)) (T : Submodule ℝ (Vsp dim))
    (h : ∀ v ∈ S, actE β v ∈ T) : ∀ v ∈ Submodule.span ℝ S, actE β v ∈ T := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => rw [actE_zero_right]; exact T.zero_mem
  | add x y _ _ hx hy => rw [actE_add_right]; exact T.add_mem hx hy
  | smul r x _ hx => rw [actE_rsmul_right]; exact T.smul_mem r hx

theorem actE_mem_span_omega {n : ℕ} (ω : Fin n → E) {β : E}
    (hβ : β ∈ Submodule.span ℚ (Set.range ω)) (x : Vsp dim) :
    actE β x ∈ Submodule.span ℝ (Set.range fun j => actE (ω j) x) := by
  induction hβ using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    exact Submodule.subset_span ⟨j, rfl⟩
  | zero => rw [actE_zero_left]; exact zero_mem _
  | add y z _ _ hy hz => rw [actE_add_left]; exact add_mem hy hz
  | smul q y _ hy => rw [actE_qsmul]; exact Submodule.smul_mem _ _ hy

variable [IsCMField E]

theorem Hf_actE (β : E) (v w : Vsp dim) :
    Hf (actE β v) w = Hf v (actE (IsCMField.complexConj E β) w) := by
  unfold Hf
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [actE_apply, map_mul, IsCMField.complexEmbedding_complexConj, Complex.conj_conj]
  ring

theorem Hf_actE' (β : E) (v w : Vsp dim) :
    Hf v (actE β w) = Hf (actE (IsCMField.complexConj E β) v) w := by
  unfold Hf
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [actE_apply, map_mul, IsCMField.complexEmbedding_complexConj]
  ring

end act

end

end ReciprocityTheory.ChartRestriction.G.I2
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SupRatioLeOfPhaseZero
namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex NumberField

noncomputable section

variable {E : Type} [Field E] [NumberField E]

theorem HC_one {dim : (E →+* ℂ) → ℕ} (v w : Vsp dim) :
    HC (n := 1) (fun _ => v) (fun _ => w) = Hf v w := by
  simp [HC]

theorem Hf_self_re {ι : Type} [Fintype ι] (v : EuclideanSpace ℂ ι) : (Hf v v).re = ‖v‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Hf, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

namespace PT

variable (X : PT E)

def toGT : GT (Idx X.dim) where
  b := X.b
  integral := X.integral
  perfect := X.perfect
  ka := fun x => (X.eps x : ℂ)
  ka_abs := fun x hx => by
    rcases X.eps_pm x hx with h | h <;> simp [h]

def col1 (s : (Fin 1 → Vsp X.dim) → ℂ) : Vsp X.dim → ℂ := fun v => s fun _ => v

theorem column_mem_sections {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1) : X.col1 s ∈ X.toGT.Sec 1 := by
  obtain ⟨hd, hf⟩ := hs
  refine (show Differentiable ℂ (X.col1 s) ∧ ∀ γ ∈ lat X.toGT.b, ∀ v, X.col1 s (v + γ) =
      X.toGT.ka γ * cexp (((1 : ℕ) : ℂ) * Real.pi * Hf v γ + ((1 : ℕ) : ℂ) * Real.pi * Hf γ γ / 2) *
        X.col1 s v from ⟨?_, ?_⟩)
  · exact hd.comp (differentiable_pi.mpr fun _ => differentiable_id)
  · intro γ hγ v
    have h := hf (fun _ => γ) (fun _ => hγ) (fun _ => v)
    simp only [HC_one, Fin.prod_univ_one, pow_one] at h
    exact h

theorem pointNormSq_column (s : (Fin 1 → Vsp X.dim) → ℂ) (a : Vsp X.dim) :
    X.ptN2 1 s (fun _ => a) = X.toGT.ptN2 1 (X.col1 s) a := by
  simp only [PT.ptN2, GT.ptN2, PT.col1, HC_one, Hf_self_re]

theorem l2_one_eq_toGT_l2_col1 (s : (Fin 1 → Vsp X.dim) → ℂ) : X.l2 1 s = X.toGT.l2 1 (X.col1 s) := by
  have hfd : X.fd 1 = (MeasurableEquiv.funUnique (Fin 1) (Vsp X.dim)) ⁻¹'
      ZSpan.fundamentalDomain X.b := by
    ext v
    simp only [PT.fd, Set.mem_setOf_eq, Set.mem_preimage]
    exact ⟨fun h => h default, fun h k => by rwa [Subsingleton.elim k default]⟩
  have hf : ∀ v : Fin 1 → Vsp X.dim, X.ptN2 1 s v =
      X.toGT.ptN2 1 (X.col1 s) (MeasurableEquiv.funUnique (Fin 1) (Vsp X.dim) v) := by
    intro v
    have hv : v = fun _ => v default := funext fun k => by rw [Subsingleton.elim k default]
    rw [hv, pointNormSq_column]
    rfl
  have hmp := MeasureTheory.volume_preserving_funUnique (Fin 1) (Vsp X.dim)
  have he := (MeasurableEquiv.funUnique (Fin 1) (Vsp X.dim)).measurableEmbedding
  unfold PT.l2 GT.l2
  rw [MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq, hfd]
  simp only [MeasureTheory.measureReal_def]
  erw [hmp.measure_preimage_emb he]
  simp_rw [hf]
  erw [hmp.setIntegral_preimage_emb he (X.toGT.ptN2 1 (X.col1 s))]
  rfl

theorem card_idx [IsCMField E] : Fintype.card (Idx X.dim) = X.gA := by
  have hinv : Function.Involutive
      (NumberField.ComplexEmbedding.conjugate : (E →+* ℂ) → (E →+* ℂ)) :=
    fun φ => RingHom.ext fun x => by simp [NumberField.ComplexEmbedding.conjugate_coe_eq]
  have hsum : ∑ τ, X.dim (NumberField.ComplexEmbedding.conjugate τ) = ∑ τ, X.dim τ :=
    Equiv.sum_comp (Function.Involutive.toPerm _ hinv) X.dim
  have h2 : 2 * ∑ τ, X.dim τ = Fintype.card (E →+* ℂ) * X.r := by
    rw [two_mul]
    nth_rewrite 2 [← hsum]
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (fun τ _ => X.dim_conj τ), Finset.sum_const,
      Finset.card_univ, smul_eq_mul]
  haveI : NumberField.IsTotallyComplex E := NumberField.IsCMField.to_isTotallyComplex
  rw [NumberField.Embeddings.card, NumberField.IsTotallyComplex.finrank] at h2
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  unfold PT.gA PT.f
  rw [NumberField.IsTotallyComplex.finrank, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  linarith

theorem firstMinimum_toTorus : X.toGT.la1 = X.la1 := rfl

end PT

theorem f_pos {X : PT E} {DF : ℕ} (P : Par X DF) : 1 ≤ PT.f E := by
  have h := P.hfr
  rcases Nat.eq_zero_or_pos (PT.f E) with h0 | h0
  · rw [h0, zero_mul] at h
    omega
  · exact h0

theorem firstMinimum_pos_bis [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) : 0 < X.la1 := by
  rw [← X.firstMinimum_toTorus]
  apply firstMinimum_pos
  rw [X.card_idx]
  have h := P.hfr
  unfold PT.gA
  omega

theorem threshold_le_firstMinimum [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) (h0 : P.ph = 0) :
    th (E := E) P.q P.R0 ≤ X.la1 := by
  by_contra hlt
  push_neg at hlt
  have hp : P.ph = 2 * PT.f E / (PT.rd E ^ 2 * X.la1 ^ 2) := by
    simp only [Par.ph, PT.ph, if_pos hlt]
  rw [hp] at h0
  have hla := firstMinimum_pos_bis P
  have hf : (1 : ℝ) ≤ PT.f E := by exact_mod_cast f_pos P
  have hrd : (16 : ℝ) ≤ PT.rd E := P.hrd
  have hpos : 0 < 2 * (PT.f E : ℝ) / (PT.rd E ^ 2 * X.la1 ^ 2) :=
    div_pos (by linarith) (mul_pos (pow_pos (by linarith) 2) (pow_pos hla 2))
  linarith

theorem one_le_sqrt_q_th {X : PT E} {DF : ℕ} (P : Par X DF) :
    1 ≤ Real.sqrt P.q * th (E := E) P.q P.R0 := by
  have hq : (0 : ℝ) < P.q := by exact_mod_cast P.hq
  have hf : (1 : ℝ) ≤ PT.f E := by exact_mod_cast f_pos P
  have hR : (270 : ℝ) ≤ P.R0 ^ 2 := P.hR0.1
  have hrd : (16 : ℝ) ≤ PT.rd E := P.hrd
  have hRR : 1 ≤ RR (E := E) := by
    unfold RR
    exact one_le_pow₀ (by linarith)
  have h3 : 1 ≤ RR (E := E) ^ 3 := one_le_pow₀ hRR
  unfold th
  rw [← Real.sqrt_mul hq.le]
  have hA : (P.q : ℝ) * (PT.f E * P.R0 ^ 2 * RR (E := E) ^ 3 / P.q) =
      PT.f E * P.R0 ^ 2 * RR (E := E) ^ 3 := by
    field_simp
  rw [hA, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
  apply Real.sqrt_le_sqrt
  have h1 : (270 : ℝ) ≤ PT.f E * P.R0 ^ 2 := by nlinarith
  nlinarith

theorem sup_ratio_le_of_phase_zero [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) (hS : GSupStatement)
    {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1) (h0 : P.ph = 0) (a : Vsp X.dim) :
    Real.sqrt (X.ptN2 1 s fun _ => a) / Real.sqrt (X.l2 1 s) ≤ Real.exp P.p1 := by
  have hN : Fintype.card (Idx X.dim) = X.gA := X.card_idx
  have hth := threshold_le_firstMinimum P h0
  have hsq := one_le_sqrt_q_th P
  have hla : 0 < X.la1 := firstMinimum_pos_bis P
  have hq : (0 : ℝ) < P.q := by exact_mod_cast P.hq
  have hsqrtq : 0 < Real.sqrt P.q := Real.sqrt_pos.mpr hq
  have hB := hS (Idx X.dim) X.toGT 1 le_rfl (X.col1 s) (X.column_mem_sections hs) a
  rw [← X.pointNormSq_column, ← X.l2_one_eq_toGT_l2_col1, X.firstMinimum_toTorus, hN] at hB
  simp only [Nat.cast_one, one_pow, one_mul, mul_one] at hB
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = 1 + 6 * Real.sqrt (X.gA * P.q) := ⟨_, rfl⟩
  have hspi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hspi1 : 1 ≤ Real.sqrt Real.pi := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
  have hs2 : Real.sqrt 2 ≤ 1.5 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have h1 : 1 ≤ Real.sqrt P.q * X.la1 :=
    le_trans hsq (mul_le_mul_of_nonneg_left hth hsqrtq.le)
  have hsN := Real.sqrt_nonneg (X.gA : ℝ)
  have hterm : 4 * Real.sqrt (2 * X.gA) / (Real.sqrt Real.pi * X.la1) ≤
      6 * Real.sqrt (X.gA * P.q) := by
    rw [div_le_iff₀ (mul_pos hspi hla), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_mul (Nat.cast_nonneg _)]
    have e1 : 4 * (Real.sqrt 2 * Real.sqrt X.gA) ≤ Real.sqrt X.gA * (6 * Real.sqrt Real.pi) := by
      nlinarith
    have e2 : Real.sqrt X.gA * (6 * Real.sqrt Real.pi) ≤
        Real.sqrt X.gA * (6 * Real.sqrt Real.pi) * (Real.sqrt P.q * X.la1) :=
      le_mul_of_one_le_right (by positivity) h1
    nlinarith
  have hBC : 1 + 4 * Real.sqrt (2 * X.gA) / (Real.sqrt Real.pi * X.la1) ≤ C := by
    rw [hC]; linarith
  have hB0 : 0 ≤ 1 + 4 * Real.sqrt (2 * X.gA) / (Real.sqrt Real.pi * X.la1) := by positivity
  have hCpos : 0 < C := by rw [hC]; positivity
  rcases le_or_gt (X.l2 1 s) 0 with hL | hL
  · rw [Real.sqrt_eq_zero'.mpr hL, div_zero]
    exact (Real.exp_pos _).le
  · have hpow := pow_le_pow_left₀ hB0 hBC (2 * X.gA)
    have hA : X.ptN2 1 s (fun _ => a) ≤ 2 * C ^ (2 * X.gA) * X.l2 1 s := by
      refine hB.trans ?_
      gcongr
    have hexp : Real.exp P.p1 = Real.exp 1 * C ^ X.gA := by
      unfold Par.p1
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (by rw [← hC]; exact hCpos), hC]
    have he2 : Real.sqrt 2 ≤ Real.exp 1 := by
      have := Real.add_one_le_exp 1
      linarith
    rw [div_le_iff₀ (Real.sqrt_pos.mpr hL), hexp]
    have hsplit : Real.sqrt (2 * C ^ (2 * X.gA) * X.l2 1 s) =
        Real.sqrt 2 * C ^ X.gA * Real.sqrt (X.l2 1 s) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
        show C ^ (2 * X.gA) = (C ^ X.gA) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    calc Real.sqrt (X.ptN2 1 s fun _ => a) ≤ Real.sqrt (2 * C ^ (2 * X.gA) * X.l2 1 s) :=
          Real.sqrt_le_sqrt hA
      _ = Real.sqrt 2 * C ^ X.gA * Real.sqrt (X.l2 1 s) := hsplit
      _ ≤ Real.exp 1 * C ^ X.gA * Real.sqrt (X.l2 1 s) := by gcongr

end

end ReciprocityTheory.ChartRestriction.G.I2
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PropABSt
namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex

noncomputable section

section

variable {ι : Type} [Fintype ι]

open Classical

def paTh (Y : GT ι) (q : ℕ) (F : EuclideanSpace ℂ ι → ℂ) : EuclideanSpace ℂ ι → ℂ :=
  fun v => ∑' γ : lat Y.b, Y.ka γ * paU q γ F v

end




end

end ReciprocityTheory.ChartRestriction.G.I2
end
