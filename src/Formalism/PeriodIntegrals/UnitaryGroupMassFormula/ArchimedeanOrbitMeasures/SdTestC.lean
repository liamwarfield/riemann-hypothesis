module

public import Lemmata.GeneralBFactThirdFurther.Imports
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.FibInvT

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.SdCoord
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.SelfDualMap
noncomputable section

namespace PI.AprimeInfW

open scoped TensorProduct
open MeasureTheory NumberField Topology Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets
  Formalism.L2.SG.Sub Matrix

theorem smul_add_tup {D : D7} (X : HidaSetting D) (g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (x y : TupI X) :
    g • (x + y) = g • x + g • y := by
  simp only [HSMul.hSMul, SMul.smul]
  funext a
  simp only [actTup, Pi.add_apply, mulVec_add]

theorem smul_neg_tup {D : D7} (X : HidaSetting D) (g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (y : TupI X) :
    g • (-y) = -(g • y) := by
  have h0 : g • (0 : TupI X) = 0 := by
    simpa using smul_add_tup X g 0 0
  have h := smul_add_tup X g (-y) y
  rw [neg_add_cancel, h0] at h
  exact eq_neg_of_add_eq_zero_left h.symm

private theorem hform_mulVec_eq_of_cT_mul_mul_eq {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
    (σ : A →+* A) (J g : Matrix n n A) (hg : Formalism.UG.cT σ g * J * g = J) (x y : n → A) :
    Formalism.UG.hform σ J (g *ᵥ x) (g *ᵥ y) = Formalism.UG.hform σ J x y := by
  have key : ∀ u v : n → A, Formalism.UG.hform σ J u v = (σ ∘ u) ⬝ᵥ (J *ᵥ v) := by
    intro u v
    first
    | simp only [Formalism.UG.hform, dotProduct, mulVec, Function.comp, Finset.mul_sum, mul_assoc]
    | simp only [Formalism.UG.hform, Matrix.dotProduct, mulVec, Function.comp, Finset.mul_sum, mul_assoc]
    | simp [Formalism.UG.hform, mulVec, Finset.mul_sum, mul_assoc]
  have hσ : σ ∘ (g *ᵥ x) = (g.map σ) *ᵥ (σ ∘ x) := by
    funext i
    exact RingHom.map_mulVec σ g x i
  have e1 : (g.map σ) *ᵥ (σ ∘ x) = (σ ∘ x) ᵥ* (g.map σ)ᵀ := (vecMul_transpose _ _).symm
  have hg' : (g.map σ)ᵀ * J * g = J := hg
  rw [key, key, hσ, e1, ← dotProduct_mulVec]
  simp only [mulVec_mulVec, ← Matrix.mul_assoc]
  rw [hg']

theorem BR_smul {D : D7} (X : HidaSetting D) (g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (x y : TupI X) :
    BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (g • x) (g • y) = BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x y := by
  simp only [HSMul.hSMul, SMul.smul]
  unfold BR
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  have hg : Formalism.UG.cT (sigR (Ainf X.B.I.F) X.B.I.cm.sig)
      (↑(HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g) : Matrix _ _ _) * JR (Ainf X.B.I.F) X.B.I.J *
      (↑(HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g) : Matrix _ _ _) = JR (Ainf X.B.I.F) X.B.I.J :=
    (show HR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J from g).2
  exact hform_mulVec_eq_of_cT_mul_mul_eq _ _ _ hg _ _

def smulAE {D : D7} (X : HidaSetting D) (g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) : TupI X ≃+ TupI X where
  toFun y := g • y
  invFun y := g⁻¹ • y
  left_inv y := inv_smul_smul g y
  right_inv y := smul_inv_smul g y
  map_add' x y := smul_add_tup X g x y

private theorem selfDual_map_of_isAddHaarMeasure {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]
    (μ : Measure V) (χ : V → V → ℂ) (em : V ≃ᵐ V) (hH : (μ.map em).IsAddHaarMeasure)
    (hχ : ∀ a b, χ (em a) (em b) = χ a b) (hneg : ∀ a, em (-a) = -(em a))
    (hcont : ∀ Φ : V → ℂ, Continuous Φ → HasCompactSupport Φ →
      Continuous (Φ ∘ em) ∧ HasCompactSupport (Φ ∘ em))
    (hμ : SelfDual μ χ) : SelfDual (μ.map em) χ := by
  refine ⟨hH, fun Φ hΦc hΦs hint z => ?_⟩
  obtain ⟨hc', hs'⟩ := hcont Φ hΦc hΦs
  have hinner : ∀ y, ∫ x, Φ x * χ x (em y) ∂(μ.map em) = ∫ x, (Φ ∘ em) x * χ x y ∂μ := by
    intro y
    rw [integral_map_equiv]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [Function.comp_apply, hχ]
  have hint' : Integrable (fun y => ∫ x, (Φ ∘ em) x * χ x y ∂μ) μ := by
    have h1 := (integrable_map_equiv em _).mp hint
    refine h1.congr (ae_of_all _ fun y => ?_)
    simp only [Function.comp_apply]
    exact hinner y
  have hz : ∀ y, χ (em y) z = χ y (em.symm z) := by
    intro y
    conv_lhs => rw [← em.apply_symm_apply z]
    exact hχ y (em.symm z)
  calc ∫ y, (∫ x, Φ x * χ x y ∂(μ.map em)) * χ y z ∂(μ.map em)
      = ∫ y, (∫ x, Φ x * χ x (em y) ∂(μ.map em)) * χ (em y) z ∂μ := integral_map_equiv em _
    _ = ∫ y, (∫ x, (Φ ∘ em) x * χ x y ∂μ) * χ y (em.symm z) ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        show (∫ x, Φ x * χ x (em y) ∂(μ.map em)) * χ (em y) z =
          (∫ x, (Φ ∘ em) x * χ x y ∂μ) * χ y (em.symm z)
        rw [hinner y, hz y]
    _ = (Φ ∘ em) (-(em.symm z)) := hμ.2 (Φ ∘ em) hc' hs' hint' (em.symm z)
    _ = Φ (-z) := by simp only [Function.comp_apply, hneg, MeasurableEquiv.apply_symm_apply]

theorem selfDual_map {D : D7} (X : HidaSetting D) (ψ : AddChar (AF X.B.I.F) ℂ) (μ : Measure (TupI X))
    (hμ : SelfDual μ (fun X' Y' : TupI X => psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J X' Y'))) (g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) :
    SelfDual (μ.map (fun y => g • y)) (fun X' Y' : TupI X => psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J X' Y')) := by
  have hc : ∀ h : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J, Continuous (fun y : TupI X => h • y) := by
    intro h
    first
    | fun_prop
    | (simp only [HSMul.hSMul, SMul.smul]; unfold actTup; fun_prop)
    | (simp only [HSMul.hSMul, SMul.smul]; unfold actTup;
        exact continuous_pi fun a => Continuous.matrix_mulVec continuous_const (continuous_apply a))
  let e : TupI X ≃ₜ TupI X :=
    { toEquiv := (smulAE X g).toEquiv
      continuous_toFun := hc g
      continuous_invFun := hc g⁻¹ }
  have hH : (μ.map e.toMeasurableEquiv).IsAddHaarMeasure := by
    haveI := hμ.1
    first
    | exact (smulAE X g).isAddHaarMeasure_map μ (hc g) (hc g⁻¹)
    | exact (smulAE X g).isAddHaarMeasure_map (hc g) (hc g⁻¹)
  exact selfDual_map_of_isAddHaarMeasure μ
    (fun X' Y' : TupI X => psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J X' Y'))
    e.toMeasurableEquiv hH
    (fun a b => by
      show psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (g • a) (g • b)) =
        psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J a b)
      rw [BR_smul])
    (fun a => smul_neg_tup X g a)
    (fun Φ hΦc hΦs => ⟨hΦc.comp e.continuous, hΦs.comp_homeomorph e⟩) hμ

def SdTestI : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    ∃ Φ : TupI X → ℂ, Continuous Φ ∧ HasCompactSupport Φ ∧
      Integrable (fun y => ∫ x, Φ x * psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x y) ∂μinf) μinf ∧
      ∃ z, Φ (-z) ≠ 0

private theorem eq_one_of_selfDual_smul {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]
    (μ : Measure V) (c : ENNReal) (hctop : c ≠ ⊤) (χ : V → V → ℂ) (hμ : SelfDual μ χ)
    (hν : SelfDual (c • μ) χ) (Φ : V → ℂ) (hc : Continuous Φ) (hs : HasCompactSupport Φ)
    (hi : Integrable (fun y => ∫ x, Φ x * χ x y ∂μ) μ) (z : V) (hz : Φ (-z) ≠ 0) : c = 1 := by
  have hin : ∀ y, ∫ x, Φ x * χ x y ∂(c • μ) = (c.toReal : ℂ) * ∫ x, Φ x * χ x y ∂μ := by
    intro y
    rw [integral_smul_measure, Complex.real_smul]
  have hi' : Integrable (fun y => ∫ x, Φ x * χ x y ∂(c • μ)) (c • μ) := by
    simp only [hin]
    exact (hi.const_mul _).smul_measure hctop
  have key := hν.2 Φ hc hs hi' z
  simp only [hin] at key
  rw [integral_smul_measure, Complex.real_smul] at key
  simp only [mul_assoc] at key
  rw [integral_const_mul, hμ.2 Φ hc hs hi z] at key
  have h2 : ((c.toReal : ℂ) * c.toReal - 1) * Φ (-z) = 0 := by linear_combination key
  have h3 : (c.toReal : ℂ) * c.toReal = 1 := by
    have h3' := (mul_eq_zero.mp h2).resolve_right hz
    linear_combination h3'
  have h4 : c.toReal * c.toReal = 1 := by exact_mod_cast h3
  have h5 : c.toReal = 1 := by
    rcases mul_self_eq_one_iff.mp h4 with h | h
    · exact h
    · linarith [ENNReal.toReal_nonneg (a := c)]
  first
  | exact (ENNReal.toReal_eq_one_iff c).mp h5
  | rw [← ENNReal.ofReal_toReal hctop, h5, ENNReal.ofReal_one]

theorem sdInvG_of (hT : SdTestI) : SdInvG := by
  unfold SdInvG
  intro D X u' ψ hT' μinf νinf fibInf hP g
  have hμ : SelfDual μinf
      (fun X' Y' : TupI X => psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J X' Y')) :=
    hP.2.2.2.2.1
  obtain ⟨Φ, hΦc, hΦs, hΦi, z, hz⟩ := hT X u' ψ hT' μinf νinf fibInf hP
  have hν := selfDual_map X ψ μinf hμ g
  haveI := hμ.1
  haveI := hν.1
  obtain ⟨c, hctop, hc⟩ : ∃ c : ENNReal, c ≠ ⊤ ∧ μinf.map (fun y => g • y) = c • μinf := by
    refine ⟨(Measure.addHaarScalarFactor (μinf.map fun y => g • y) μinf : ENNReal), ENNReal.coe_ne_top,
      (Measure.isAddLeftInvariant_eq_smul (μinf.map fun y => g • y) μinf).trans ?_⟩
    ext s _
    simp [Measure.smul_apply]
  rw [hc] at hν
  rw [hc]
  have hc1 : c = 1 :=
    eq_one_of_selfDual_smul μinf c hctop _ hμ hν Φ hΦc hΦs hΦi z hz
  rw [hc1, one_smul]

end PI.AprimeInfW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.SdTest
noncomputable section

namespace PI.AprimeInfW.ST

open MeasureTheory

def TestExP {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (μ : Measure V)
    (χ : V → V → ℂ) : Prop :=
  ∃ Φ : V → ℂ, Continuous Φ ∧ HasCompactSupport Φ ∧
    Integrable (fun y => ∫ x, Φ x * χ x y ∂μ) μ ∧ ∃ z, Φ (-z) ≠ 0

open MeasureTheory Complex Filter Topology

theorem char_real (f : ℝ → ℂ) (hc : Continuous f) (hadd : ∀ s t, f (s + t) = f s * f t)
    (hn : ∀ s, ‖f s‖ = 1) : ∃ b : ℝ, ∀ s : ℝ, f s = exp (↑(b * s) * I) := by
  first | exact Bl.general_b_fact_third_further.goal1 .. | (apply Bl.general_b_fact_third_further.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_third_further.goal1 <;> assumption)

theorem freq_unique {u v : ℝ} (h : ∀ s : ℝ, exp (↑(u * s) * I) = exp (↑(v * s) * I)) : u = v := by
  by_contra huv
  have hne : u - v ≠ 0 := sub_ne_zero.2 huv
  have h1 := h (Real.pi / (u - v))
  have h2 : exp (↑((u - v) * (Real.pi / (u - v))) * I) = 1 := by
    have : (↑((u - v) * (Real.pi / (u - v))) : ℂ) * I =
        ↑(u * (Real.pi / (u - v))) * I - ↑(v * (Real.pi / (u - v))) * I := by
      push_cast; ring
    rw [this, Complex.exp_sub, h1, div_self (Complex.exp_ne_zero _)]
  rw [mul_div_cancel₀ _ hne, Complex.exp_pi_mul_I] at h2
  norm_num at h2

section Bichar

open scoped RealInnerProductSpace

variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

structure IsBichar (χ : W → W → ℂ) : Prop where
  addL : ∀ x x' y, χ (x + x') y = χ x y * χ x' y
  addR : ∀ x y y', χ x (y + y') = χ x y * χ x y'
  norm1 : ∀ x y, ‖χ x y‖ = 1
  contL : ∀ y, Continuous fun x => χ x y
  contR : ∀ x, Continuous (χ x)

theorem IsBichar.zero_left {χ : W → W → ℂ} (h : IsBichar χ) (y : W) : χ 0 y = 1 := by
  have hne : χ 0 y ≠ 0 := fun h0 => by have := h.norm1 0 y; rw [h0, norm_zero] at this; exact zero_ne_one this
  have e := h.addL 0 0 y
  rw [add_zero] at e
  exact mul_left_cancel₀ hne (by rw [mul_one]; exact e.symm)

theorem IsBichar.freq {χ : W → W → ℂ} (h : IsBichar χ) (v y : W) :
    ∃ β : ℝ, ∀ s : ℝ, χ (s • v) y = exp (↑(β * s) * I) :=
  char_real (fun s => χ (s • v) y) ((h.contL y).comp (continuous_id.smul continuous_const))
    (fun s t => by simp only [add_smul]; exact h.addL _ _ y) (fun s => h.norm1 _ y)

theorem arg_exp_small {θ : ℝ} (h : θ ∈ Set.Ioo (-Real.pi) Real.pi) : arg (exp (↑θ * I)) = θ := by
  rw [arg_exp_mul_I, toIocMod_eq_self]
  exact ⟨h.1, by linarith [h.2, Real.pi_pos]⟩

theorem measurable_freq {χ : W → W → ℂ} (h : IsBichar χ) (v : W) (β : W → ℝ)
    (hβ : ∀ y, ∀ s : ℝ, χ (s • v) y = exp (↑(β y * s) * I)) : Measurable β := by
  let g : ℕ → W → ℝ := fun m y => ((m : ℝ) + 1) * arg (χ ((1 / ((m : ℝ) + 1)) • v) y)
  have hg : ∀ m, Measurable (g m) := fun m =>
    measurable_const.mul (measurable_arg.comp (h.contR _).measurable)
  refine measurable_of_tendsto_metrizable hg (tendsto_pi_nhds.2 fun y => ?_)
  have ht : Tendsto (fun m : ℕ => β y * (1 / ((m : ℝ) + 1))) atTop (𝓝 (β y * 0)) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (β y)
  rw [mul_zero] at ht
  have hev := ht (Ioo_mem_nhds (neg_lt_zero.2 Real.pi_pos) Real.pi_pos)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hev] with m hm
  simp only [g]
  rw [hβ y, arg_exp_small hm]
  field_simp

theorem freq_add {χ : W → W → ℂ} (h : IsBichar χ) (v : W) (β : W → ℝ)
    (hβ : ∀ y, ∀ s : ℝ, χ (s • v) y = exp (↑(β y * s) * I)) (y y' : W) :
    β (y + y') = β y + β y' := by
  refine freq_unique fun s => ?_
  rw [← hβ, h.addR, hβ, hβ, ← Complex.exp_add]
  congr 1; push_cast; ring

theorem bichar_eq {χ : W → W → ℂ} (h : IsBichar χ) :
    ∃ L : W →L[ℝ] W, ∀ x y, χ x y = (Real.fourierChar ⟪x, L y⟫ : ℂ) := by
  classical
  choose β hβ using fun v y => h.freq v y
  let b := stdOrthonormalBasis ℝ W
  have hm : ∀ j, Measurable (fun y => β (b j) y) := fun j =>
    measurable_freq h (b j) _ (fun y => hβ (b j) y)
  have ha : ∀ j y y', β (b j) (y + y') = β (b j) y + β (b j) y' := fun j =>
    freq_add h (b j) (fun y => β (b j) y) (fun y => hβ (b j) y)
  let Lf : W → W := fun y => ∑ j, (β (b j) y / (2 * Real.pi)) • b j
  let Lm : W →+ W := AddMonoidHom.mk' Lf fun y y' => by
    simp only [Lf, ha, add_div, add_smul, Finset.sum_add_distrib]
  have hLm : Measurable Lm := by
    show Measurable fun y => ∑ j, (β (b j) y / (2 * Real.pi)) • b j
    exact Finset.measurable_sum Finset.univ fun j _ => ((hm j).div_const _).smul_const (b j)
  have hLc : Continuous Lm := Measure.AddMonoidHom.continuous_of_measurable Lm hLm
  refine ⟨Lm.toRealLinearMap hLc, fun x y => ?_⟩
  have hprod : ∀ s : Finset (Fin (Module.finrank ℝ W)),
      χ (∑ j ∈ s, ⟪b j, x⟫ • b j) y = ∏ j ∈ s, χ (⟪b j, x⟫ • b j) y := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [h.zero_left]
    | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, h.addL, ih]
  have e1 : χ x y = χ (∑ j, ⟪b j, x⟫ • b j) y := by rw [b.sum_repr' x]
  rw [e1, hprod]
  have e2 : ∀ j, χ (⟪b j, x⟫ • b j) y = exp (↑(β (b j) y * ⟪b j, x⟫) * I) := fun j => hβ _ _ _
  simp only [e2]
  rw [← Complex.exp_sum, Real.fourierChar_apply]
  congr 1
  have hLy : ⟪x, (Lm.toRealLinearMap hLc) y⟫ = ∑ j, β (b j) y / (2 * Real.pi) * ⟪b j, x⟫ := by
    show ⟪x, Lf y⟫ = _
    simp only [Lf, inner_sum, inner_smul_right]
    exact Finset.sum_congr rfl fun j _ => by rw [real_inner_comm]
  rw [hLy]
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  field_simp

end Bichar

section Tests

open scoped RealInnerProductSpace FourierTransform SchwartzMap ContDiff

variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

theorem testEx_kernel (μ : Measure W) [μ.IsAddHaarMeasure] (χ : W → W → ℂ)
    (hadd : ∀ x x' y, χ (x + x') y = χ x y * χ x' y) (hc : ∀ y, Continuous fun x => χ x y)
    (t : W) (ht0 : t ≠ 0) (ht : ∀ y, χ t y = 1) : TestExP μ χ := by
  have hpos : 0 < ‖t‖ := norm_pos_iff.2 ht0
  let f : ContDiffBump (0 : W) := ⟨‖t‖ / 4, ‖t‖ / 2, by positivity, by linarith⟩
  let φ : W → ℂ := fun x => ((f x : ℝ) : ℂ)
  have hφc : Continuous φ := Complex.continuous_ofReal.comp f.continuous
  have hφs : HasCompactSupport φ := f.hasCompactSupport.comp_left Complex.ofReal_zero
  let Φ : W → ℂ := fun x => φ (x + t) - φ x
  have hΦc : Continuous Φ := (hφc.comp (continuous_id.add continuous_const)).sub hφc
  have hΦs : HasCompactSupport Φ := by
    have h1 : HasCompactSupport fun x => φ (x + t) := hφs.comp_homeomorph (Homeomorph.addRight t)
    exact h1.sub hφs
  have hT : ∀ y, ∫ x, Φ x * χ x y ∂μ = 0 := by
    intro y
    let g : W → ℂ := fun x => φ x * χ x y
    have hg : Integrable g μ := (hφc.mul (hc y)).integrable_of_hasCompactSupport hφs.mul_right
    have e : (fun x => Φ x * χ x y) = fun x => g (x + t) - g x := by
      funext x; simp only [Φ, g, hadd, ht, mul_one, sub_mul]
    rw [e, integral_sub (hg.comp_add_right t) hg, integral_add_right_eq_self, sub_self]
  refine ⟨Φ, hΦc, hΦs, ?_, 0, ?_⟩
  · have e : (fun y => ∫ x, Φ x * χ x y ∂μ) = fun _ => 0 := funext hT
    rw [e]; exact integrable_zero _ _ _
  · simp only [Φ, φ, neg_zero, zero_add]
    rw [f.zero_of_le_dist (by rw [dist_zero_right]; show ‖t‖ / 2 ≤ ‖t‖; linarith),
      f.one_of_mem_closedBall (Metric.mem_closedBall_self (by positivity))]
    norm_num

theorem testEx_fourier (μ : Measure W) [μ.IsAddHaarMeasure] (A : W ≃L[ℝ] W) :
    TestExP μ (fun x y => (Real.fourierChar ⟪x, A y⟫ : ℂ)) := by
  let f : ContDiffBump (0 : W) := ⟨1, 2, one_pos, one_lt_two⟩
  let φ : W → ℂ := fun x => ((f x : ℝ) : ℂ)
  have hφd : ContDiff ℝ ∞ φ := Complex.ofRealCLM.contDiff.comp f.contDiff
  have hφs : HasCompactSupport φ := f.hasCompactSupport.comp_left Complex.ofReal_zero
  let S : 𝓢(W, ℂ) := hφs.toSchwartzMap hφd
  let B : W ≃L[ℝ] W := A.trans (ContinuousLinearEquiv.neg ℝ)
  set c : NNReal := μ.addHaarScalarFactor volume
  have hμ : μ = c • volume := Measure.isAddLeftInvariant_eq_smul μ volume
  have hT : ∀ y, ∫ x, φ x * (Real.fourierChar ⟪x, A y⟫ : ℂ) ∂μ =
      ((c : ℝ) : ℂ) * (𝓕 S : 𝓢(W, ℂ)) (B y) := by
    intro y
    rw [hμ, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
    congr 1
    rw [SchwartzMap.fourier_coe, Real.fourier_eq]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp [B, S, φ, inner_neg_right, Circle.smul_def, mul_comm]
  have hB : (Measure.map B μ).IsAddHaarMeasure := B.isAddHaarMeasure_map μ
  have hI : Integrable (fun y => (𝓕 S : 𝓢(W, ℂ)) (B y)) μ := by
    have h1 : Integrable (𝓕 S : 𝓢(W, ℂ)) (Measure.map B μ) := (𝓕 S).integrable
    exact (integrable_map_measure h1.aestronglyMeasurable B.continuous.measurable.aemeasurable).1 h1
  refine ⟨φ, hφd.continuous, hφs, ?_, 0, ?_⟩
  · have e : (fun y => ∫ x, φ x * (Real.fourierChar ⟪x, A y⟫ : ℂ) ∂μ) =
        fun y => ((c : ℝ) : ℂ) * (𝓕 S : 𝓢(W, ℂ)) (B y) := funext hT
    rw [e]; exact hI.const_mul _
  · simp only [φ, neg_zero]
    rw [f.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]
    norm_num

theorem testEx_bichar (μ : Measure W) [μ.IsAddHaarMeasure] {χ : W → W → ℂ} (h : IsBichar χ) :
    TestExP μ χ := by
  obtain ⟨L, hL⟩ := bichar_eq h
  by_cases hs : Function.Surjective L
  · have hi : Function.Injective L :=
      (LinearMap.injective_iff_surjective (f := (L : W →ₗ[ℝ] W))).2 hs
    let A : W ≃L[ℝ] W :=
      (LinearEquiv.ofBijective (L : W →ₗ[ℝ] W) ⟨hi, hs⟩).toContinuousLinearEquiv
    have e : χ = fun x y => (Real.fourierChar ⟪x, A y⟫ : ℂ) :=
      funext₂ fun x y => by rw [hL x y]; rfl
    rw [e]; exact testEx_fourier μ A
  · have hK : (LinearMap.range (L : W →ₗ[ℝ] W))ᗮ ≠ ⊥ := by
      rw [Ne, Submodule.orthogonal_eq_bot_iff, LinearMap.range_eq_top]; exact hs
    obtain ⟨t, htK, ht0⟩ := (Submodule.ne_bot_iff _).1 hK
    refine testEx_kernel μ χ h.addL h.contL t ht0 fun y => ?_
    have h0 : ⟪t, L y⟫ = 0 :=
      (Submodule.mem_orthogonal' _ t).1 htK _ (LinearMap.mem_range_self (L : W →ₗ[ℝ] W) y)
    rw [hL, h0, AddChar.map_zero_eq_one, Circle.coe_one]

theorem testEx_of_homeo {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (χ : V → V → ℂ)
    (e : V ≃ₜ W) (he : ∀ x y, e (x + y) = e x + e y)
    (hL : ∀ x x' y, χ (x + x') y = χ x y * χ x' y) (hR : ∀ x y y', χ x (y + y') = χ x y * χ x y')
    (hn : ∀ x y, ‖χ x y‖ = 1) (hcL : ∀ y, Continuous fun x => χ x y)
    (hcR : ∀ x, Continuous (χ x)) : TestExP μ χ := by
  let ea : V ≃+ W := AddEquiv.mk' e.toEquiv he
  have hs : ∀ u v : W, e.symm (u + v) = e.symm u + e.symm v := fun u v => ea.symm.map_add u v
  let ce : V ≃ₜ+ W :=
    { ea with continuous_toFun := e.continuous, continuous_invFun := e.symm.continuous }
  let em : V ≃ᵐ W := e.toMeasurableEquiv
  let μ' : Measure W := Measure.map em μ
  have : μ'.IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map μ ce
  let χ' : W → W → ℂ := fun x y => χ (e.symm x) (e.symm y)
  have hb : IsBichar χ' :=
    { addL := fun x x' y => by simp only [χ', hs, hL]
      addR := fun x y y' => by simp only [χ', hs, hR]
      norm1 := fun x y => hn _ _
      contL := fun y => (hcL _).comp e.symm.continuous
      contR := fun x => (hcR _).comp e.symm.continuous }
  obtain ⟨φ, hφc, hφs, hI, z, hz⟩ := testEx_bichar μ' hb
  have hT : ∀ y, ∫ x, φ (e x) * χ x y ∂μ = ∫ x, φ x * χ' x (e y) ∂μ' := by
    intro y
    rw [integral_map_equiv em]
    simp [χ', em]
  refine ⟨fun x => φ (e x), hφc.comp e.continuous, hφs.comp_homeomorph e, ?_, e.symm z, ?_⟩
  · show Integrable (fun y => ∫ x, φ (e x) * χ x y ∂μ) μ
    have e1 : (fun y => ∫ x, φ (e x) * χ x y ∂μ) = (fun y => ∫ x, φ x * χ' x y ∂μ') ∘ em :=
      funext hT
    rw [e1]
    exact (integrable_map_equiv em _).1 hI
  · show φ (e (-e.symm z)) ≠ 0
    have h1 : e (-e.symm z) = -z := by
      have := ea.map_neg (e.symm z)
      change e (-e.symm z) = -e (e.symm z) at this
      rw [this, e.apply_symm_apply]
    rw [h1]; exact hz

end Tests

end PI.AprimeInfW.ST
end
end

noncomputable section

namespace PI.AprimeInfW

open scoped TensorProduct
open MeasureTheory NumberField Topology Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets
  Formalism.L2.SG.Sub Matrix

section Coord

variable {F : Type} [Field F] [NumberField F]

def complReal (v : InfinitePlace F) (hv : v.IsReal) : v.Completion ≃ₜ ℝ :=
  (InfinitePlace.Completion.ringEquivRealOfIsReal hv).toEquiv.toHomeomorphOfIsInducing (by
    have hf : (⇑(InfinitePlace.Completion.ringEquivRealOfIsReal hv).toEquiv) =
        ⇑(InfinitePlace.Completion.extensionEmbeddingOfIsReal hv) :=
      funext fun x => InfinitePlace.Completion.ringEquivRealOfIsReal_apply hv x
    rw [hf]
    exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.isInducing)

theorem complReal_add (v : InfinitePlace F) (hv : v.IsReal) (x y : v.Completion) :
    complReal v hv (x + y) = complReal v hv x + complReal v hv y :=
  map_add (InfinitePlace.Completion.ringEquivRealOfIsReal hv) x y

def ainfReal (hF : ∀ v : InfinitePlace F, v.IsReal) : InfiniteAdeleRing F ≃ₜ (InfinitePlace F → ℝ) :=
  Homeomorph.piCongrRight fun v => complReal v (hF v)

theorem ainfReal_add (hF : ∀ v : InfinitePlace F, v.IsReal) (x y : InfiniteAdeleRing F) :
    ainfReal hF (x + y) = ainfReal hF x + ainfReal hF y := by
  funext v
  exact complReal_add v (hF v) (x v) (y v)

end Coord

section Tens

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]

def tensCoord : R ⊗[F] E ≃ₜ (Module.Free.ChooseBasisIndex R (R ⊗[F] E) → R) :=
  let e := (Module.Free.chooseBasis R (R ⊗[F] E)).equivFun
  { toEquiv := e.toEquiv
    continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }

theorem tensCoord_add (x y : R ⊗[F] E) : tensCoord R (x + y) = tensCoord R x + tensCoord R y :=
  map_add (Module.Free.chooseBasis R (R ⊗[F] E)).equivFun x y

end Tens

def flat4 (A B C P : Type) [Fintype A] [Fintype B] [Fintype C] [Fintype P] :
    (A → B → C → P → ℝ) ≃ₜ EuclideanSpace ℝ (A × B × C × P) where
  toFun f := (EuclideanSpace.equiv (A × B × C × P) ℝ).symm (fun k => f k.1 k.2.1 k.2.2.1 k.2.2.2)
  invFun u a b c d := (EuclideanSpace.equiv (A × B × C × P) ℝ u) (a, b, c, d)
  left_inv f := by funext a b c d; simp
  right_inv u := by ext k; simp
  continuous_toFun := (EuclideanSpace.equiv (A × B × C × P) ℝ).symm.continuous.comp (continuous_pi fun k =>
    (continuous_apply k.2.2.2).comp ((continuous_apply k.2.2.1).comp ((continuous_apply k.2.1).comp
      (continuous_apply k.1))))
  continuous_invFun := continuous_pi fun a => continuous_pi fun b => continuous_pi fun c => continuous_pi fun d =>
    (continuous_apply (a, b, c, d)).comp (EuclideanSpace.equiv (A × B × C × P) ℝ).continuous

theorem flatten_four_add (A B C P : Type) [Fintype A] [Fintype B] [Fintype C] [Fintype P] (f g : A → B → C → P → ℝ) :
    flat4 A B C P (f + g) = flat4 A B C P f + flat4 A B C P g := by
  ext k
  simp [flat4]

end PI.AprimeInfW
end
end

noncomputable section

namespace PI.AprimeInfW

open scoped TensorProduct
open MeasureTheory NumberField Topology Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets
  Formalism.L2.SG.Sub Matrix

theorem totReal_of {D : D7} (X : HidaSetting D) : ∀ v : InfinitePlace X.B.I.F, v.IsReal :=
  fun v => X.B.I.cm.totReal.isReal v

def tupCoord {D : D7} (X : HidaSetting D) :
    TupI X ≃ₜ EuclideanSpace ℝ (Fin (D.R.rS + 1 + D.R.rS) × Fin X.B.I.n ×
      Module.Free.ChooseBasisIndex (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) × InfinitePlace X.B.I.F) :=
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  (Homeomorph.piCongrRight fun _ => Homeomorph.piCongrRight fun _ =>
    (tensCoord (F := X.B.I.F) (E := X.B.I.E) (Ainf X.B.I.F)).trans
      (Homeomorph.piCongrRight fun _ => ainfReal (totReal_of X))).trans (flat4 _ _ _ _)

theorem tupCoord_add {D : D7} (X : HidaSetting D) (x y : TupI X) :
    tupCoord X (x + y) = tupCoord X x + tupCoord X y := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  simp only [tupCoord, Homeomorph.trans_apply]
  rw [← flatten_four_add]
  congr 1
  funext a i k
  simp only [Homeomorph.piCongrRight_apply, Homeomorph.trans_apply, Pi.add_apply]
  rw [tensCoord_add]
  exact ainfReal_add (totReal_of X) _ _

theorem psiInf_addP {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (a b : Ainf F) :
    psiInf F ψ (a + b) = psiInf F ψ a * psiInf F ψ b := by
  have h : (pairA F (a + b) 0 : AF F) = pairA F a 0 + pairA F b 0 := by
    show ((a + b, 0) : Ainf F × Af F) = ((a, 0) : Ainf F × Af F) + ((b, 0) : Ainf F × Af F)
    rw [Prod.mk_add_mk, add_zero]
  simp only [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.psiInf]
  rw [h, AddChar.map_add_eq_mul]

theorem psiInf_eq {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hS : Formalism.L2.SG.LocVol.IsStdChar ψ) :
    psiInf F ψ = fun x => Complex.exp (2 * Real.pi * Complex.I *
      ((∑ w : InfinitePlace F, (InfinitePlace.Completion.extensionEmbedding w (x w)).re : ℝ) : ℂ)) :=
  funext hS

theorem continuous_psiInfP {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (hS : Formalism.L2.SG.LocVol.IsStdChar ψ) : Continuous (psiInf F ψ) := by
  rw [psiInf_eq ψ hS]
  refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp ?_))
  exact continuous_finsetSum _ fun w _ => Complex.continuous_re.comp
    ((InfinitePlace.Completion.isometry_extensionEmbedding (v := w)).continuous.comp (continuous_apply w))

theorem norm_psiInfP {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (hS : Formalism.L2.SG.LocVol.IsStdChar ψ) (x : Ainf F) : ‖psiInf F ψ x‖ = 1 := by
  rw [hS x]
  have : 2 * (Real.pi : ℂ) * Complex.I *
      ((∑ w : InfinitePlace F, (InfinitePlace.Completion.extensionEmbedding w (x w)).re : ℝ) : ℂ) =
      ((2 * Real.pi * ∑ w : InfinitePlace F, (InfinitePlace.Completion.extensionEmbedding w (x w)).re : ℝ) : ℂ) *
        Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

theorem BR_add_leftP {D : D7} (X : HidaSetting D) (x x' y : TupI X) :
    BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (x + x') y = BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x y + BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x' y := by
  simp only [BR, hR, Formalism.UG.hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem BR_add_rightP {D : D7} (X : HidaSetting D) (x y y' : TupI X) :
    BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x (y + y') = BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x y + BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x y' := by
  simp only [BR, hR, Formalism.UG.hform, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem continuous_traceP {D : D7} (X : HidaSetting D) :
    Continuous (Algebra.trace (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  exact IsModuleTopology.continuous_of_linearMap _

theorem continuous_BR_leftP {D : D7} (X : HidaSetting D) (y : TupI X) : Continuous fun x : TupI X => BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x y := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  show Continuous fun x : TupI X => ∑ a, Algebra.trace (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)
    (∑ i, ∑ j, sigR (Ainf X.B.I.F) X.B.I.cm.sig (x a i) * JR (Ainf X.B.I.F) X.B.I.J i j * y a j)
  exact continuous_finsetSum _ fun a _ => (continuous_traceP X).comp (continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ => (((continuous_sigRP (Ainf X.B.I.F) X.B.I.cm.sig).comp
      ((continuous_apply i).comp (continuous_apply a))).mul continuous_const).mul continuous_const)

theorem continuous_BR_rightP {D : D7} (X : HidaSetting D) (x : TupI X) : Continuous fun y : TupI X => BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x y := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  show Continuous fun y : TupI X => ∑ a, Algebra.trace (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)
    (∑ i, ∑ j, sigR (Ainf X.B.I.F) X.B.I.cm.sig (x a i) * JR (Ainf X.B.I.F) X.B.I.J i j * y a j)
  exact continuous_finsetSum _ fun a _ => (continuous_traceP X).comp (continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ => continuous_const.mul ((continuous_apply j).comp (continuous_apply a)))

theorem sdTestI_holds : SdTestI := by
  intro D X u' ψ hT μinf νinf fibInf hP
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  haveI := hP.2.2.2.2.1.1
  have hS := hP.2.2.1
  have hpc := continuous_psiInfP ψ hS
  exact ST.testEx_of_homeo μinf _ (tupCoord X) (tupCoord_add X)
    (fun x x' y => by rw [BR_add_leftP, psiInf_addP])
    (fun x y y' => by rw [BR_add_rightP, psiInf_addP])
    (fun x y => norm_psiInfP ψ hS _)
    (fun y => hpc.comp (continuous_BR_leftP X y))
    (fun x => hpc.comp (continuous_BR_rightP X x))

theorem invFib_holds : InvFib := invFib_of (sdInvG_of sdTestI_holds)

end PI.AprimeInfW
