module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsScalarStableLatticeAutomorphismFundamental
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiComplexifiedKEquivariance
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordOfMemXa
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LebesgueCommonStabilizerEqRadicalLeviMap

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeftQuotientCovolumeWithDensityDetNormSq
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeftQuotientCovolumeWithDensityDetNormSq
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.DetSlab

variable (E : Type) [Field E] [NumberField E] (j : ℕ)

theorem detNorm_mul (x y : MatInf E j) : detNorm E j (x * y) = detNorm E j x * detNorm E j y := by
  unfold detNorm
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have : Matrix.of ((x * y) w) = Matrix.of (x w) * Matrix.of (y w) := rfl
  rw [this, Matrix.det_mul, norm_mul, mul_pow]

theorem detNorm_nonneg (x : MatInf E j) : 0 ≤ detNorm E j x :=
  Finset.prod_nonneg fun _ _ => sq_nonneg _

theorem detNorm_aut (hE : IsTotallyComplex E) (Λ : Submodule (𝓞 E) (Fin j → E)) (hΛ : Submodule.IsFullLattice E Λ)
    {x : MatInf E j} (hx : x ∈ autGL E j Λ) : detNorm E j x = 1 := by
  obtain ⟨γ, hγ, hx⟩ := hx
  have h1 : IsIntegral ℤ (γ : Matrix (Fin j) (Fin j) E).det :=
    GlobalTheory.Mem.StabDet.isIntegral_det Λ hΛ.fg (Submodule.IsFullLattice.span_eq_top (self := hΛ)) _ fun v hv => (hγ v).2 hv
  have h2 : IsIntegral ℤ ((γ⁻¹ : GL (Fin j) E) : Matrix (Fin j) (Fin j) E).det :=
    GlobalTheory.Mem.StabDet.isIntegral_det Λ hΛ.fg (Submodule.IsFullLattice.span_eq_top (self := hΛ)) _ fun v hv => (hγ _).1 (by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]; exact hv)
  have h3 : (γ : Matrix (Fin j) (Fin j) E).det * ((γ⁻¹ : GL (Fin j) E) : Matrix (Fin j) (Fin j) E).det = 1 := by
    rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
  let u : (𝓞 E)ˣ := Units.mkOfMulEqOne ⟨_, h1⟩ ⟨_, h2⟩ (RingOfIntegers.ext h3)
  have h4 := InfinitePlace.prod_eq_abs_norm ((u : 𝓞 E) : E)
  rw [NumberField.Units.norm] at h4
  have hu : ((u : 𝓞 E) : E) = (γ : Matrix (Fin j) (Fin j) E).det := rfl
  rw [hu] at h4
  unfold detNorm
  rw [Rat.cast_one] at h4
  rw [← h4]
  refine Finset.prod_congr rfl fun w _ => ?_
  have h5 : Matrix.of (x w) = w.embedding.mapMatrix (γ : Matrix (Fin j) (Fin j) E) := by
    ext a b
    simpa using hx w a b
  rw [h5, ← RingHom.map_det, InfinitePlace.norm_embedding_eq, (IsTotallyComplex.isComplex w).mult_eq_two]

theorem continuous_detNorm :
    Continuous (fun x : InfinitePlace E → Fin j → Fin j → ℂ => detNorm E j x) := by
  unfold detNorm
  refine continuous_finsetProd _ fun w _ => ?_
  exact (Continuous.matrix_det (continuous_apply w)).norm.pow 2

theorem measurable_detNorm : Measurable (detNorm E j) := (continuous_detNorm E j).measurable

def scal (t : ℝ) (x : MatInf E j) : MatInf E j := fun w a b => (t : ℂ) * x w a b

theorem measurable_scal (t : ℝ) : Measurable (scal E j t) :=
  (continuous_const_smul t : Continuous fun x : InfinitePlace E → Fin j → Fin j → ℂ => t • x).measurable

theorem detNorm_scal (t : ℝ) (x : MatInf E j) :
    detNorm E j (scal E j t x) = |t| ^ (2 * j * Fintype.card (InfinitePlace E)) * detNorm E j x := by
  unfold detNorm
  have : ∀ w, Matrix.of (scal E j t x w) = (t : ℂ) • Matrix.of (x w) := fun w => rfl
  simp only [this, Matrix.det_smul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, mul_pow,
    Finset.prod_mul_distrib, Finset.prod_const, Fintype.card_fin, Finset.card_univ, ← pow_mul]
  rw [mul_comm j 2]

theorem isAddHaar_volume : (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)).IsAddHaarMeasure := by
  haveI h1 : (volume : Measure (Fin j → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI h2 : (volume : Measure (Fin j → Fin j → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  exact Measure.pi.isAddHaarMeasure _

theorem lintegral_scal (t : ℝ) (ht : t ≠ 0) (f : MatInf E j → ENNReal) (hf : Measurable f) :
    ∫⁻ x, f (scal E j t x) ∂(haarGL E j) = ∫⁻ x, f x ∂(haarGL E j) := by
  have hd : Measurable fun x : InfinitePlace E → Fin j → Fin j → ℂ => ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j) :=
    (((measurable_detNorm E j).inv).pow_const j).ennreal_ofReal
  have hf' : Measurable (fun x : InfinitePlace E → Fin j → Fin j → ℂ => f x) := hf
  have hf'' : Measurable (fun x : InfinitePlace E → Fin j → Fin j → ℂ => f (t • x)) :=
    hf.comp (measurable_scal E j t)
  have e1 := lintegral_withDensity_eq_lintegral_mul (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)) hd hf'
  have e2 := lintegral_withDensity_eq_lintegral_mul (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)) hd hf''
  refine e2.trans (Eq.trans ?_ e1.symm)
  haveI := isAddHaar_volume E j
  have hm := Measure.map_addHaar_smul (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)) ht
  have hrk : Module.finrank ℝ (InfinitePlace E → Fin j → Fin j → ℂ) =
      2 * j * Fintype.card (InfinitePlace E) * j := by
    simp only [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
    ring
  have e3 := lintegral_map (μ := (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ))) (hd.mul hf')
    (measurable_const_smul t)
  rw [hm, lintegral_smul_measure, hrk, smul_eq_mul] at e3
  set N := 2 * j * Fintype.card (InfinitePlace E) with hN
  have hpos : 0 < |t| ^ (N * j) := pow_pos (abs_pos.2 ht) _
  have e4 : ∀ x : InfinitePlace E → Fin j → Fin j → ℂ, ENNReal.ofReal ((detNorm E j (t • x))⁻¹ ^ j) =
      ENNReal.ofReal |(t ^ (N * j))⁻¹| * ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j) := by
    intro x
    have h : detNorm E j (t • x) = |t| ^ N * detNorm E j x := detNorm_scal E j t x
    rw [← ENNReal.ofReal_mul (abs_nonneg _), h, abs_inv, abs_pow, mul_inv, mul_pow,
      inv_pow, ← pow_mul]
  have e5 := lintegral_const_mul (μ := (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)))
    (ENNReal.ofReal |(t ^ (N * j))⁻¹|) (hd.mul hf'')
  replace e3 := e3.trans ((lintegral_congr fun x => (congrArg (· * f (scal E j t x)) (e4 x)).trans
    (mul_assoc _ _ _)).trans e5)
  have hne : ENNReal.ofReal |(t ^ (N * j))⁻¹| ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le, abs_inv, abs_pow]; exact inv_pos.2 hpos
  exact ((ENNReal.mul_right_inj hne ENNReal.ofReal_ne_top).1 e3).symm

theorem restrict_pos (hj : 1 ≤ j) : (haarGL E j).restrict {g | 0 < detNorm E j g} = haarGL E j := by
  refine Measure.restrict_eq_self_of_ae_mem ?_
  have hd : Measurable fun x : InfinitePlace E → Fin j → Fin j → ℂ => ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j) :=
    (((measurable_detNorm E j).inv).pow_const j).ennreal_ofReal
  refine (ae_withDensity_iff hd).2 (Filter.Eventually.of_forall fun x hx => ?_)
  refine lt_of_le_of_ne (detNorm_nonneg E j x) fun h => hx ?_
  rw [← h, _root_.inv_zero, zero_pow (by omega), ENNReal.ofReal_zero]

theorem sFinite_haarGL : SFinite (haarGL E j) := by
  haveI := isAddHaar_volume E j
  exact (Measure.withDensity.instSFinite :
    SFinite (Measure.withDensity (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)) _))

theorem lintegral_exp (F : ℝ → ENNReal) :
    ∫⁻ u, F (Real.exp u) = ∫⁻ t in Set.Ioi (0 : ℝ), F t / ENNReal.ofReal t := by
  have h := lintegral_image_eq_lintegral_abs_deriv_mul (s := Set.univ) (f := Real.exp) (f' := Real.exp)
    MeasurableSet.univ (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn
    (fun t => F t / ENNReal.ofReal t)
  rw [Set.image_univ, Real.range_exp, Measure.restrict_univ] at h
  rw [h]
  refine lintegral_congr fun u => ?_
  rw [abs_of_pos (Real.exp_pos u), ENNReal.mul_div_cancel
    (by simpa using Real.exp_pos u) ENNReal.ofReal_ne_top]

theorem lintegral_cone (hj : 1 ≤ j) (D : Set (MatInf E j)) (hD : MeasurableSet D)
    (hpos : D ⊆ {g | 0 < detNorm E j g}) (hsc : ∀ g ∈ D, ∀ t : ℝ, 0 < t → scal E j t g ∈ D)
    (F : ℝ → ENNReal) (hF : Measurable F) :
    ∫⁻ g in D, F (detNorm E j g) ∂(haarGL E j) =
      haarGL E j ({x | 1 ≤ detNorm E j x ∧ detNorm E j x < Real.exp 1} ∩ D) *
        ∫⁻ t in Set.Ioi (0 : ℝ), F t / ENNReal.ofReal t := by
  haveI := sFinite_haarGL E j
  have hl : Measurable fun g => Real.log (detNorm E j g) := Real.measurable_log.comp (measurable_detNorm E j)
  set ν : Measure ℝ := ((haarGL E j).restrict D).map fun g => Real.log (detNorm E j g) with hν
  have hνa : ∀ s, MeasurableSet s → ν s = haarGL E j ((fun g => Real.log (detNorm E j g)) ⁻¹' s ∩ D) :=
    fun s hs => by rw [hν, Measure.map_apply hl hs, Measure.restrict_apply (hl hs)]
  set N := 2 * j * Fintype.card (InfinitePlace E) with hN
  have hN0 : (N : ℝ) ≠ 0 := by
    have : 0 < N := Nat.mul_pos (by omega) Fintype.card_pos
    exact_mod_cast this.ne'
  haveI : ν.IsAddLeftInvariant := by
    refine ⟨fun c => ?_⟩
    ext s hs
    have hc : Measurable fun u : ℝ => c + u := measurable_const_add c
    rw [Measure.map_apply hc hs, hνa _ (hc hs), hνa _ hs]
    have hA : MeasurableSet ((fun g => Real.log (detNorm E j g)) ⁻¹' s ∩ D) := (hl hs).inter hD
    have hB : MeasurableSet ((fun g => Real.log (detNorm E j g)) ⁻¹' ((fun u => c + u) ⁻¹' s) ∩ D) :=
      (hl (hc hs)).inter hD
    have ht : 0 < Real.exp (c / N) := Real.exp_pos _
    rw [← lintegral_indicator_one hA, ← lintegral_indicator_one hB,
      ← lintegral_scal E j _ ht.ne' _ (measurable_one.indicator hA)]
    refine lintegral_congr fun x => ?_
    have hback : scal E j (Real.exp (c / N))⁻¹ (scal E j (Real.exp (c / N)) x) = x := by
      funext w a b
      simp only [scal]
      rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ ht.ne', Complex.ofReal_one, one_mul]
    have hlog : x ∈ D → Real.log (detNorm E j (scal E j (Real.exp (c / N)) x)) =
        c + Real.log (detNorm E j x) := fun hx => by
      have h0 : 0 < detNorm E j x := hpos hx
      rw [detNorm_scal, abs_of_pos ht, Real.log_mul (pow_pos ht _).ne' h0.ne', Real.log_pow, Real.log_exp, ← hN,
        mul_div_cancel₀ _ hN0]
    refine (Set.indicator_const_eq_indicator_const (c := (1 : ENNReal)) ⟨fun h => ⟨?_, hsc _ h.2 _ ht⟩, fun h => ?_⟩)
    · have := h.1
      simp only [Set.mem_preimage] at this ⊢
      rwa [hlog h.2]
    · have hx : x ∈ D := hback ▸ hsc _ h.2 _ (inv_pos.2 ht)
      refine ⟨?_, hx⟩
      have := h.1
      simp only [Set.mem_preimage] at this ⊢
      rwa [hlog hx] at this
  have hv : (volume : Measure ℝ) (Set.Ico 0 1) = 1 := by simp
  have hFe : Measurable fun u => F (Real.exp u) := hF.comp Real.measurable_exp
  have h1 := measure_add_lintegral_eq volume ν (s := Set.Ico 0 1) measurableSet_Ico _ hFe
  simp only [measure_preimage_add_right] at h1
  rw [hv, one_mul, lintegral_const_mul _ (f := fun u => F (Real.exp (-u))) (hFe.comp measurable_neg), lintegral_neg_eq_self (fun u => F (Real.exp u)),
    hνa _ measurableSet_Ico] at h1
  have hset : (fun g => Real.log (detNorm E j g)) ⁻¹' Set.Ico 0 1 ∩ D =
      {x | 1 ≤ detNorm E j x ∧ detNorm E j x < Real.exp 1} ∩ D := by
    ext x
    refine and_congr_left fun hx => ?_
    have h0 : 0 < detNorm E j x := hpos hx
    simp only [Set.mem_preimage, Set.mem_Ico, Set.mem_setOf_eq]
    rw [Real.log_nonneg_iff h0, Real.log_lt_iff_lt_exp h0]
  rw [hset] at h1
  have h2 : ∫⁻ u, F (Real.exp u) ∂ν = ∫⁻ g in D, F (detNorm E j g) ∂(haarGL E j) := by
    rw [hν, lintegral_map hFe hl]
    refine setLIntegral_congr_fun hD fun x hx => ?_
    simp only [Real.exp_log (hpos hx)]
  rw [← h2, h1, lintegral_exp]

theorem covol_withDensity_detNorm : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ (j : ℕ), 1 ≤ j → ∀ Λ : Submodule (𝓞 E) (Fin j → E), Submodule.IsFullLattice E Λ → ∀ F : ℝ → ENNReal, Measurable F → covol (autGL E j Λ) ((haarGL E j).withDensity fun x => F (detNorm E j x)) {x | 0 < detNorm E j x} = covol (autGL E j Λ) (haarGL E j) {x | 1 ≤ detNorm E j x ∧ detNorm E j x < Real.exp 1} * ∫⁻ t in Set.Ioi (0 : ℝ), F t / ENNReal.ofReal t := by
  intro E _ _ hE j hj Λ hΛ F hF
  obtain ⟨D, hD, hpos, -, hsc, hcov⟩ :=
    GlobalTheory.T.exists_scalarStable_latticeAutomorphismFundamentalDomain E hE j Λ hΛ
  have hm := measurable_detNorm E j
  have hP : MeasurableSet {g : MatInf E j | 0 < detNorm E j g} := measurableSet_lt measurable_const hm
  have hS : MeasurableSet {x : MatInf E j | 1 ≤ detNorm E j x ∧ detNorm E j x < Real.exp 1} :=
    (measurableSet_le measurable_const hm).inter (measurableSet_lt hm measurable_const)
  have hinv : ∀ γ ∈ autGL E j Λ, ∀ g, detNorm E j (γ * g) = detNorm E j g := fun γ hγ g => by
    rw [detNorm_mul, detNorm_aut E j hE Λ hΛ hγ, one_mul]
  have h1 := hcov (fun x => F (detNorm E j x)) _ ((hF.comp hm).indicator hP)
    (fun γ hγ g _ => by simp only [hinv γ hγ g]) hP subset_rfl
    (fun γ hγ g hg => by simpa only [Set.mem_setOf_eq, hinv γ hγ g] using hg)
  have h2 := hcov (fun _ => 1) _ (measurable_const.indicator hP) (fun _ _ _ _ => rfl) hS
    (fun g hg => lt_of_lt_of_le one_pos hg.1)
    (fun γ hγ g hg => by simpa only [Set.mem_setOf_eq, hinv γ hγ g] using hg)
  rw [restrict_pos E j hj] at h1 h2
  rw [withDensity_const, one_smul, setLIntegral_one] at h2
  rw [h1, h2, Set.inter_eq_right.2 hpos]
  exact lintegral_cone E j hj D hD hpos hsc F hF

end GlobalTheory.DetSlab
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeftQuotientCovolumeWithDensityDetNormSqStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leftQuotientCovolume_withDensity_detNormSq : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ (j : ℕ), 1 ≤ j → ∀ Λ : Submodule (𝓞 E) (Fin j → E), Submodule.IsFullLattice E Λ → ∀ F : ℝ → ENNReal, Measurable F → covol (autGL E j Λ) ((haarGL E j).withDensity fun x => F (detNorm E j x)) {x | 0 < detNorm E j x} = covol (autGL E j Λ) (haarGL E j) {x | 1 ≤ detNorm E j x ∧ detNorm E j x < Real.exp 1} * ∫⁻ t in Set.Ioi (0 : ℝ), F t / ENNReal.ofReal t := by
  intro E _ _ hE j hj Λ hΛ F hF
  first
  | exact GlobalTheory.DetSlab.covol_withDensity_detNorm E hE j hj Λ hΛ F hF
  | exact GlobalTheory.DetSlab.covol_withDensity_detNorm E hE j hj Λ hΛ.toIsLattice F hF
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiRestrictionHolomorphicNearOne
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiRestrictionHolomorphicNearOne
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec Filter Topology
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.Dec.Local

theorem eventually_eq_zero_of_fixed {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] (σ : E → E)
    (hadd : ∀ x y, σ (x + y) = σ x + σ y) (hsmul : ∀ (c : ℂ) x, σ (c • x) = star c • σ x)
    (hinv : ∀ x, σ (σ x) = x) (hcont : Continuous σ) (x₀ : E) (hx₀ : σ x₀ = x₀) (f : E → F)
    (hf : ∀ᶠ x in 𝓝 x₀, DifferentiableAt ℂ f x ∧ (σ x = x → f x = 0)) :
    ∀ᶠ x in 𝓝 x₀, f x = 0 := by
  let u : E → E := fun x => (1 / 2 : ℂ) • (x + σ x)
  let v : E → E := fun x => (-Complex.I / 2 : ℂ) • x + (Complex.I / 2 : ℂ) • σ x
  have hu : ∀ x, σ (u x) = u x := by
    intro x
    simp only [u, hsmul, hadd, hinv]
    rw [add_comm]; simp
  have hv : ∀ x, σ (v x) = v x := by
    intro x
    simp only [v, hsmul, hadd, hinv]
    rw [add_comm]; simp
  have huv : ∀ x, u x + Complex.I • v x = x := by
    intro x
    simp only [u, v]
    match_scalars <;> (ring_nf; try simp) <;> norm_num
  have hG : Continuous fun p : E × ℂ => u p.1 + p.2 • v p.1 := by
    simp only [u, v]; fun_prop
  have h0 : ∀ t : ℂ, u x₀ + t • v x₀ = x₀ := by
    intro t
    simp only [u, v, hx₀]
    match_scalars; ring
  have htube : ∀ᶠ x in 𝓝 x₀, ∀ t ∈ Metric.closedBall (0 : ℂ) 2,
      DifferentiableAt ℂ f (u x + t • v x) ∧ (σ (u x + t • v x) = u x + t • v x → f (u x + t • v x) = 0) := by
    apply (isCompact_closedBall (0 : ℂ) 2).eventually_forall_of_forall_eventually
    intro t _
    have := hG.tendsto (x₀, t)
    simp only [h0] at this
    exact this.eventually hf
  filter_upwards [htube] with x hx
  have hd : DifferentiableOn ℂ (fun t : ℂ => f (u x + t • v x)) (Metric.ball 0 2) := by
    intro t ht
    exact ((hx t (Metric.ball_subset_closedBall ht)).1.comp t (by fun_prop)).differentiableWithinAt
  have hfr : ∃ᶠ t in 𝓝[≠] (0 : ℂ), f (u x + t • v x) = 0 := by
    have ht : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · exact (Complex.continuous_ofReal.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        simpa using hs
    refine ht.frequently (Eventually.frequently ?_)
    have hb : ∀ᶠ s : ℝ in 𝓝[≠] 0, s ∈ Metric.closedBall (0 : ℝ) 2 :=
      nhdsWithin_le_nhds (Metric.closedBall_mem_nhds 0 two_pos)
    filter_upwards [hb] with s hs
    refine (hx s (by simpa using hs)).2 ?_
    rw [hadd, hu, hsmul, hv]; simp
  have := (hd.analyticOnNhd Metric.isOpen_ball).eqOn_zero_of_preconnected_of_frequently_eq_zero
    (convex_ball (0 : ℂ) 2).isPreconnected (Metric.mem_ball_self two_pos) hfr
    (show Complex.I ∈ Metric.ball (0 : ℂ) 2 by simp)
  simpa [huv] using this

theorem differentiableAt_of_coef {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (f : E → (W →L[ℂ] W)) (x : E)
    (hf : ∀ u v : W, DifferentiableAt ℂ (fun y => ⟪u, f y v⟫_ℂ) x) : DifferentiableAt ℂ f x := by
  let b := stdOrthonormalBasis ℂ W
  have e : f = fun y => ∑ i, ∑ j, ⟪b i, f y (b j)⟫_ℂ • (innerSL ℂ (b j)).smulRight (b i) := by
    funext y
    ext v
    conv_lhs => rw [← b.sum_repr' v, ← b.sum_repr' (f y _)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, inner_sum, inner_smul_right, _root_.sum_apply,
      _root_.smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
      Finset.sum_smul, smul_smul]
    simp only [mul_comm]
  rw [e]
  refine DifferentiableAt.fun_sum fun i _ => DifferentiableAt.fun_sum fun j _ => ?_
  exact (hf _ _).smul_const _

open scoped Matrix.Norms.L2Operator

variable {n : ℕ}

def prJ (ε : Fin n → Bool) (a : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • (a + Jm ε * a * Jm ε)

theorem prJ_comm (ε : Fin n → Bool) (a : Matrix (Fin n) (Fin n) ℂ) : prJ ε a * Jm ε = Jm ε * prJ ε a := by
  simp only [prJ, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc,
    Jm_mul_self, Matrix.mul_one]
  rw [← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul, add_comm]

theorem prJ_of_comm {ε : Fin n → Bool} {a : Matrix (Fin n) (Fin n) ℂ} (h : a * Jm ε = Jm ε * a) :
    prJ ε a = a := by
  rw [prJ, ← h, Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one]
  match_scalars; norm_num

theorem prJ_one (ε : Fin n → Bool) : prJ ε 1 = 1 := prJ_of_comm (by simp)

theorem prJ_conjTranspose (ε : Fin n → Bool) (a : Matrix (Fin n) (Fin n) ℂ) : prJ ε aᴴ = (prJ ε a)ᴴ := by
  simp [prJ, Jm_conjTranspose, Matrix.mul_assoc]

theorem differentiable_prJ (ε : Fin n → Bool) : Differentiable ℂ (prJ ε) := by
  unfold prJ; fun_prop

theorem eventually_isUnit : ∀ᶠ a in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), IsUnit a :=
  Units.isOpen.mem_nhds isUnit_one

theorem eventually_prJ_mem (ε : Fin n → Bool) : ∀ᶠ a in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), prJ ε a ∈ KC ε := by
  have := ((differentiable_prJ ε).continuous.tendsto' 1 1 (prJ_one ε)).eventually eventually_isUnit
  filter_upwards [this] with a ha
  exact ⟨ha, prJ_comm ε a⟩

theorem posDef_mul_conjTranspose {c : Matrix (Fin n) (Fin n) ℂ} (hc : IsUnit c) : (c * cᴴ).PosDef := by
  rw [(Matrix.posSemidef_self_mul_conjTranspose c).posDef_iff_isUnit]
  exact hc.mul (by simpa [Matrix.star_eq_conjTranspose] using hc.star)

theorem posDef_exp {X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ = X) : (NormedSpace.exp X).PosDef := by
  have hY : ((1 / 2 : ℂ) • X)ᴴ = (1 / 2 : ℂ) • X := by simp [hX]
  have e : X = (1 / 2 : ℂ) • X + (1 / 2 : ℂ) • X := by match_scalars; norm_num
  have := posDef_mul_conjTranspose (Matrix.isUnit_exp ((1 / 2 : ℂ) • X))
  rwa [exp_conjTranspose_of_hermitian hY, ← exp_add_self, ← e] at this

variable {ε : Fin n → Bool} {lam : Fin n → ℝ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)} {w : W}

theorem eventually_differentiableAt_tau {abelian₂ : Fin n → ℝ} (hτ : IsTau ε abelian₂ τ w) :
    ∀ᶠ a in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), DifferentiableAt ℂ (fun y => τ (prJ ε y)) a := by
  haveI := hτ.1
  filter_upwards [(eventually_prJ_mem ε).eventually_nhds] with a ha
  refine differentiableAt_of_coef _ _ fun u v => ?_
  have h : DifferentiableOn ℂ (fun y : Matrix (Fin n) (Fin n) ℂ => ⟪u, τ y v⟫_ℂ) (KC ε) := hτ.2.2.1 u v
  have h2 : DifferentiableOn ℂ (fun y : Matrix (Fin n) (Fin n) ℂ => ⟪u, τ (prJ ε y) v⟫_ℂ)
      {y | prJ ε y ∈ KC ε} :=
    h.comp (differentiable_prJ ε).differentiableOn fun y hy => hy
  exact h2.differentiableAt ha

theorem eventually_ps_mul (hB : PsBasic) (hE : PsEquiv) (hl : IsHCParam lam) (hτ : IsTau ε (lowK ε lam) τ w) :
    ∀ᶠ x : (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) ×
        (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) in 𝓝 ((1, 1), (1, 1)),
      ps ε lam τ w (prJ ε x.1.1 * (x.1.2 * x.2.2) * prJ ε x.2.1) -
        τ (prJ ε x.1.1) * ps ε lam τ w (x.1.2 * x.2.2) * τ (prJ ε x.2.1) = 0 := by
  haveI := hτ.1
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  obtain ⟨hopen, hpos, hdiff, -⟩ := hB n ε lam W τ w hl hτ
  have hopen' : IsOpen (U1 ε) := hopen
  have hdiff' : DifferentiableOn ℂ (ps ε lam τ w) (U1 ε) := hdiff
  have hps : ∀ᶠ z in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), DifferentiableAt ℂ (ps ε lam τ w) z := by
    filter_upwards [hopen'.mem_nhds (hpos 1 Matrix.PosDef.one)] with z hz
    exact hdiff'.differentiableAt (hopen'.mem_nhds hz)
  have hP := differentiable_prJ ε
  refine eventually_eq_zero_of_fixed (fun x => ((x.2.1ᴴ, x.2.2ᴴ), (x.1.1ᴴ, x.1.2ᴴ))) ?_ ?_ ?_ ?_ _ ?_ _ ?_
  · intro x y; simp
  · intro c x; simp
  · intro x; simp
  · fun_prop
  · simp
  · let E := (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) ×
        (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ)
    have d1 : Differentiable ℂ fun x : E => prJ ε x.1.1 * (x.1.2 * x.2.2) * prJ ε x.2.1 := by
      fun_prop
    have d2 : Differentiable ℂ fun x : E => x.1.2 * x.2.2 := by fun_prop
    have d3 : Differentiable ℂ fun x : E => x.1.1 := by fun_prop
    have d4 : Differentiable ℂ fun x : E => x.2.1 := by fun_prop
    have d5 : Differentiable ℂ fun x : E => x.1.2 := by fun_prop
    filter_upwards [(d1.continuous.tendsto' ((1, 1), (1, 1)) 1 (by simp [prJ_one])).eventually hps,
      (d2.continuous.tendsto' ((1, 1), (1, 1)) 1 (by simp)).eventually hps,
      (d3.continuous.tendsto' ((1, 1), (1, 1)) 1 rfl).eventually (eventually_differentiableAt_tau hτ),
      (d4.continuous.tendsto' ((1, 1), (1, 1)) 1 rfl).eventually (eventually_differentiableAt_tau hτ),
      (d3.continuous.tendsto' ((1, 1), (1, 1)) 1 rfl).eventually (eventually_prJ_mem ε),
      (d5.continuous.tendsto' ((1, 1), (1, 1)) 1 rfl).eventually eventually_isUnit] with x h1 h2 h3 h4 h5 h6
    have k1 := DifferentiableAt.comp (𝕜 := ℂ) (g := ps ε lam τ w) (f := fun x : E => prJ ε x.1.1 * (x.1.2 * x.2.2) * prJ ε x.2.1)
      x h1 (d1 x)
    have k2 := DifferentiableAt.comp (𝕜 := ℂ) (g := ps ε lam τ w) (f := fun x : E => x.1.2 * x.2.2) x h2 (d2 x)
    have k3 := DifferentiableAt.comp (g := fun y => τ (prJ ε y)) (𝕜 := ℂ) (f := fun x : E => x.1.1) x h3 (d3 x)
    have k4 := DifferentiableAt.comp (g := fun y => τ (prJ ε y)) (𝕜 := ℂ) (f := fun x : E => x.2.1) x h4 (d4 x)
    refine ⟨k1.sub ((k3.mul k2).mul k4), ?_⟩
    intro hx
    have e1 : x.2.1 = x.1.1ᴴ := (congrArg (fun y => y.2.1) hx).symm
    have e2 : x.2.2 = x.1.2ᴴ := (congrArg (fun y => y.2.2) hx).symm
    rw [e1, e2, prJ_conjTranspose, hE n ε lam W τ w hl hτ _ _ (posDef_mul_conjTranspose h6) h5, sub_eq_zero]
    rfl

theorem psLocal_of (hB : PsBasic) (hE : PsEquiv) : PsLocal := by
  intro n ε lam W _ _ τ w hl hτ
  obtain ⟨hopen, hpos, -, -⟩ := hB n ε lam W τ w hl hτ
  have hopen' : IsOpen (U1 ε) := hopen
  have hu : Continuous fun g : UJ ε => umat g := (isClosedEmbeddingMatrix n ε).1.continuous
  have hu1 : umat (1 : UJ ε) = 1 := rfl
  obtain ⟨L, hLc, hL⟩ := (polar_decomposition_holds n ε).2.2
  have hdec : ∀ g : Matrix (Fin n) (Fin n) ℂ, g * NormedSpace.exp (-L g) * NormedSpace.exp (L g) = g := by
    intro g
    rw [Matrix.mul_assoc, matrix_exp_neg_mul_exp, Matrix.mul_one]
  have h1U : inUJ ε 1 := by simp [inUJ]
  have hL1 : L 1 = 0 := by
    refine ((polar_decomposition_holds n ε).2.1 _ 1 _ 0 (hL 1 h1U).2 ⟨one_mem _, by simp⟩ (hL 1 h1U).1
      (by simp [inP, inG]) ?_).2
    rw [hdec]; simp
  have hLc' : Continuous fun g : UJ ε => L (umat g) := hLc.comp_continuous hu fun g => g.2
  have hexp : Continuous (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _) := by
    letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
    exact NormedSpace.exp_continuous
  have hc : Continuous fun g : UJ ε =>
      (((umat g * NormedSpace.exp (-L (umat g)), NormedSpace.exp (L (umat g))), (1, 1)) :
        (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) ×
          (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ)) :=
    ((hu.mul (hexp.comp hLc'.neg)).prodMk (hexp.comp hLc')).prodMk continuous_const
  filter_upwards [(hu.tendsto' 1 1 hu1).eventually (hopen'.mem_nhds (hpos 1 Matrix.PosDef.one)),
    (hc.tendsto' 1 ((1, 1), (1, 1)) (by simp [hu1, hL1])).eventually (eventually_ps_mul hB hE hl hτ)]
    with g hg1 hg2
  refine ⟨hg1, ?_⟩
  obtain ⟨hX, hk⟩ := hL (umat g) g.2
  simp only [prJ_one, prJ_of_comm hk.2, mul_one, hτ.2.1.1, hdec, sub_eq_zero] at hg2
  rw [hg2]
  conv_lhs => rw [← hdec (umat g)]
  exact Psi_unitary_mul ε lam τ w hk.1 (posDef_exp (hermitian_of_mem_hermitian_part hX))

end GlobalTheory.Dec.Local

theorem GlobalTheory.Dec.psLocal : PsLocal := GlobalTheory.Dec.Local.psLocal_of GlobalTheory.T.psi_holomorphic_near_positive_matrices_at_one GlobalTheory.T.psi_complexifiedK_equivariance
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiRestrictionHolomorphicNearOneStatement
open GlobalTheory.Dec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_restriction_holomorphic_near_one : PsLocal := by
  first | exact @GlobalTheory.Dec.psLocal | exact GlobalTheory.Dec.psLocal | (intros; apply GlobalTheory.Dec.psLocal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiPolarDecompositionEquivariance
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiPolarDecompositionEquivariance
open Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.Dec.PsiPolarProof

variable {n : ℕ}

lemma exp_posDef_of_herm {X : Matrix (Fin n) (Fin n) ℂ} (h : Xᴴ = X) : (NormedSpace.exp X).PosDef := by
  have hY : ((1 / 2 : ℝ) • X)ᴴ = (1 / 2 : ℝ) • X := by
    rw [Matrix.conjTranspose_smul, h]; simp
  have e : X = (1 / 2 : ℝ) • X + (1 / 2 : ℝ) • X := by rw [← add_smul]; norm_num
  have e2 : NormedSpace.exp X =
      (NormedSpace.exp ((1 / 2 : ℝ) • X))ᴴ * NormedSpace.exp ((1 / 2 : ℝ) • X) := by
    rw [exp_conjTranspose_of_hermitian hY, ← exp_add_self, ← e]
  rw [e2]
  exact Matrix.PosDef.conjTranspose_mul_self _
    (Matrix.mulVec_injective_of_isUnit (Matrix.isUnit_exp _))

lemma mem_KC_of_mem_K {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    k ∈ KC ε :=
  ⟨⟨⟨k, star k, Unitary.mul_star_self_of_mem hk.1, Unitary.star_mul_self_of_mem hk.1⟩, rfl⟩, hk.2⟩

lemma mul_mem_K {ε : Fin n → Bool} {k k' : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε)
    (hk' : k' ∈ Kset ε) : k * k' ∈ Kset ε :=
  ⟨mul_mem hk.1 hk'.1, by rw [Matrix.mul_assoc, hk'.2, ← Matrix.mul_assoc, hk.2, Matrix.mul_assoc]⟩

lemma star_mem_K {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    kᴴ ∈ Kset ε := by
  refine ⟨Unitary.star_mem hk.1, ?_⟩
  have := congrArg Matrix.conjTranspose hk.2
  simpa [Matrix.conjTranspose_mul, Jm_conjTranspose] using this.symm

theorem psiPolar_of (hB : PsBasic) (hE : PsEquiv) : PsiPolar := by
  intro n ε lam W _ _ τ w hl hτ
  refine ⟨fun k hk X hX => Psi_unitary_mul ε lam τ w hk.1
    (exp_posDef_of_herm (hermitian_of_mem_hermitian_part hX)), ?_, ?_⟩
  · have h := Psi_unitary_mul ε lam τ w (one_mem _) (Matrix.PosDef.one (n := Fin n) (R := ℂ))
    rw [Matrix.mul_one] at h
    rw [h, (hB n ε lam W τ w hl hτ).2.2.2, hτ.2.1.1]
    rfl
  · intro k₁ h₁ k₂ h₂ g hg
    obtain ⟨k, X, hk, hX, rfl⟩ := (polar_decomposition_holds n ε).1 g hg
    have hp := exp_posDef_of_herm (hermitian_of_mem_hermitian_part hX)
    set p := NormedSpace.exp X
    have hs : k₂ * k₂ᴴ = 1 := Unitary.mul_star_self_of_mem h₂.1
    have hc := mem_KC_of_mem_K (star_mem_K h₂)
    have hq : (k₂ᴴ * p * k₂).PosDef :=
      hp.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit (mem_KC_of_mem_K h₂).1)
    have e : k₁ * (k * p) * k₂ = (k₁ * k * k₂) * (k₂ᴴ * p * k₂) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc k₂ k₂ᴴ, hs, Matrix.one_mul]
    have hk3 := mul_mem_K (mul_mem_K h₁ hk) h₂
    have he := hE n ε lam W τ w hl hτ p k₂ᴴ hp hc
    rw [Matrix.conjTranspose_conjTranspose] at he
    rw [e, Psi_unitary_mul ε lam τ w hk3.1 hq, Psi_unitary_mul ε lam τ w hk.1 hp, he,
      ← ContinuousLinearMap.comp_assoc]
    have hm : (τ (k₁ * k * k₂)).comp (τ k₂ᴴ) = (τ k₁).comp (τ k) := by
      have a := hτ.2.1.2 _ (mem_KC_of_mem_K hk3) _ hc
      have b := hτ.2.1.2 _ (mem_KC_of_mem_K h₁) _ (mem_KC_of_mem_K hk)
      rw [Matrix.mul_assoc, hs, Matrix.mul_one] at a
      exact a.symm.trans b
    rw [hm]
    rfl

end GlobalTheory.Dec.PsiPolarProof

theorem GlobalTheory.Dec.psiPolar : GlobalTheory.Dec.PsiPolar :=
  GlobalTheory.Dec.PsiPolarProof.psiPolar_of GlobalTheory.T.psi_holomorphic_near_positive_matrices_at_one GlobalTheory.T.psi_complexifiedK_equivariance
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiPolarDecompositionEquivarianceStatement
open GlobalTheory.Dec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_polar_decomposition_equivariance : PsiPolar := by
  first | exact @GlobalTheory.Dec.psiPolar | exact GlobalTheory.Dec.psiPolar | (intros; apply GlobalTheory.Dec.psiPolar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsConjGaugeInvariant
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso

def innerAutTop {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (s : G) : G ≃ₜ* G :=
  { MulAut.conj s with
    continuous_toFun := by
      change Continuous fun g : G => s * g * s⁻¹
      fun_prop
    continuous_invFun := by
      change Continuous fun g : G => s⁻¹ * g * s
      fun_prop }

theorem inUJ_map_conj {n : ℕ} (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) :
    Formalism.REAL.inUJ ε (g.map (starRingEnd ℂ)) := by
  unfold Formalism.REAL.inUJ at hg ⊢
  have hJ : (Formalism.REAL.Jm ε).map (starRingEnd ℂ) = Formalism.REAL.Jm ε := by
    ext i j
    simp only [Formalism.REAL.Jm, Matrix.map_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  have hH : (g.map (starRingEnd ℂ))ᴴ = gᴴ.map (starRingEnd ℂ) := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  have h2 := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M.map (starRingEnd ℂ)) hg
  simp only [Matrix.map_mul, hJ] at h2
  rw [hH]
  exact h2

noncomputable def conjUJHom {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.UJ ε →* Formalism.REAL.UJ ε :=
  ((Units.map ((starRingEnd ℂ).mapMatrix (m := Fin n)).toMonoidHom).comp (Formalism.REAL.UJ ε).subtype).codRestrict
    (Formalism.REAL.UJ ε) fun g => inUJ_map_conj ε g.2

theorem uMat_conjUJHom {n : ℕ} (ε : Fin n → Bool) (g : Formalism.REAL.UJ ε) :
    uMat (conjUJHom ε g) = (uMat g).map (starRingEnd ℂ) := rfl

theorem conjUJHom_invol {n : ℕ} (ε : Fin n → Bool) (g : Formalism.REAL.UJ ε) : conjUJHom ε (conjUJHom ε g) = g := by
  apply Subtype.ext
  apply Units.ext
  show uMat (conjUJHom ε (conjUJHom ε g)) = uMat g
  rw [uMat_conjUJHom, uMat_conjUJHom]
  ext i j
  simp

theorem continuous_conjUJHom {n : ℕ} (ε : Fin n → Bool) : Continuous (conjUJHom ε) := by
  have hc : Continuous ((starRingEnd ℂ).mapMatrix (m := Fin n)).toMonoidHom := by
    show Continuous fun M : Matrix (Fin n) (Fin n) ℂ => M.map (starRingEnd ℂ)
    exact Continuous.matrix_map continuous_id Complex.continuous_conj
  have hu := Continuous.units_map _ hc
  exact Continuous.subtype_mk (hu.comp continuous_subtype_val) _

noncomputable def conjUJ {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.UJ ε ≃ₜ* Formalism.REAL.UJ ε where
  toFun := conjUJHom ε
  invFun := conjUJHom ε
  left_inv := conjUJHom_invol ε
  right_inv := conjUJHom_invol ε
  map_mul' := map_mul _
  continuous_toFun := continuous_conjUJHom ε
  continuous_invFun := continuous_conjUJHom ε

theorem gauge_map_inner_comp {n : ℕ} (ε : Fin n → Bool) (C : Formalism.REAL.UJ ε ≃ₜ* Formalism.REAL.UJ ε)
    (hC : ∀ g, Formalism.REAL.hs (uMat (C g) - 1) = Formalism.REAL.hs (uMat g - 1)) (s : Formalism.REAL.UJ ε) (c : ℝ)
    (hc : IsGauge ε c) :
    (ENNReal.ofReal c • Formalism.REAL.muG ε).map (fun g => s * C g * s⁻¹) = ENNReal.ofReal c • Formalism.REAL.muG ε := by
  have hT : ∀ g, (C.trans (innerAutTop s)) (C.symm s⁻¹ * g * (C.symm s⁻¹)⁻¹) = C g := by
    intro g
    show s * C (C.symm s⁻¹ * g * (C.symm s⁻¹)⁻¹) * s⁻¹ = C g
    simp only [map_mul, map_inv, C.apply_symm_apply]
    group
  have key := gauge_map_of_iso n n ε ε rfl (C.trans (innerAutTop s)) (C.symm s⁻¹)
    (fun g => by rw [hT]; exact hC g) c c hc hc
  have hf : (fun g => s * C g * s⁻¹) = ⇑(C.trans (innerAutTop s)) := by
    funext g
    rfl
  rw [hf]
  exact key

theorem exists_conj_gauge_invariant : ∀ (n : ℕ) (ε : Fin n → Bool) (τ : ℂ →+* ℂ), (τ = RingHom.id ℂ ∨ τ = starRingEnd ℂ) → ∃ C : Formalism.REAL.UJ ε ≃ₜ* Formalism.REAL.UJ ε, (∀ g, uMat (C g) = (uMat g).map τ) ∧ ∀ (s : Formalism.REAL.UJ ε) (c : ℝ), IsGauge ε c → (ENNReal.ofReal c • Formalism.REAL.muG ε).map (fun g => s * C g * s⁻¹) = ENNReal.ofReal c • Formalism.REAL.muG ε := by
  intro n ε τ hτ
  rcases hτ with rfl | rfl
  · refine ⟨ContinuousMulEquiv.refl _, fun g => ?_, fun s c hc => ?_⟩
    · ext i j
      simp
    · exact gauge_map_inner_comp ε (ContinuousMulEquiv.refl _) (fun g => rfl) s c hc
  · refine ⟨conjUJ ε, fun g => uMat_conjUJHom ε g, fun s c hc => ?_⟩
    refine gauge_map_inner_comp ε (conjUJ ε) (fun g => ?_) s c hc
    have h1 : uMat (conjUJ ε g) = (uMat g).map (starRingEnd ℂ) := uMat_conjUJHom ε g
    rw [h1]
    unfold Formalism.REAL.hs
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have e : ((uMat g).map (starRingEnd ℂ) - 1) i j = starRingEnd ℂ ((uMat g - 1) i j) := by
      rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.map_apply, map_sub]
      congr 1
      simp only [Matrix.one_apply]
      split_ifs <;> simp
    rw [e, Complex.norm_conj]

end GlobalTheory.LeviIso
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealFrameAutomorphismUnitriangularRowsCoords
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealFrameAutomorphismUnitriangularRowsCoords
noncomputable section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

namespace GlobalTheory.DegVol.RefCovTop

theorem upperIn_of_zero {r : ℕ} (β : Fin r → ℕ) : upperIn β 0 = 1 := by
  ext a b
  by_cases h : a < b
  · simp [upperIn, upper, h, ne_of_lt h]
  · simp [upperIn, upper, h, Matrix.one_apply]

private theorem uEmb_one' (k r : ℕ) : uEmb k r (1 : Matrix (Fin r) (Fin r) ℂ) = 1 := by
  ext i j
  unfold uEmb
  simp only [inv_one, Matrix.one_apply]
  split_ifs <;> simp_all [Fin.ext_iff]
  omega

theorem crd_of_zero {k r j : ℕ} (β : Fin r → ℕ) (q : (UTin β → ℂ) × PTop k r j) (h : q.1 = 0) :
    crd k r j β q = pTop k r j q.2 := by
  rw [crd, h, upperIn_of_zero, uEmb_one', Matrix.mul_one]

private theorem mulVec_bvec_lemma_2 {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (M *ᵥ bvec j) i = M i j := by
  simp [Matrix.mulVec, dotProduct, bvec, Pi.single_apply]

private theorem eI_inj' {k r : ℕ} (a c : Fin r) : eI k r a = eI k r c ↔ a = c := by
  constructor
  · intro h
    have h' := congrArg Fin.val h
    exact Fin.ext h'
  · rintro rfl
    rfl

private theorem wI_ne_esI' {k r : ℕ} (l : Fin (k + 1)) (b : Fin r) : wI k r l ≠ esI k r b := by
  intro h
  have h0 := congrArg Fin.val h
  have h1 : (wI k r l).val = r + l.val := rfl
  have h2 : (esI k r b).val = 2 * r + k - b.val := rfl
  have := l.isLt
  have := b.isLt
  omega

private theorem pTop_mulVec_eq_of_vanishing {k r j : ℕ} (q : PTop k r j) (w : Fin (2 * r + k + 1) → ℂ)
    (hw : ∀ m : Fin (2 * r + k + 1), r ≤ m.val → w m = 0) : pTop k r j q *ᵥ w = w := by
  funext i
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single i]
  · simp [pTop, pOf, pEl]
  · intro m _ hmi
    by_cases hm : r ≤ m.val
    · simp [hw m hm]
    · have hz : pTop k r j q i m = 0 := by
        unfold pTop pOf pEl
        rw [if_neg (Ne.symm hmi), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega)]
      simp [hz]
  · simp

private theorem pTop_wI_esI_eq {k r j : ℕ} (q : PTop k r j) (b : Fin r) (hb : j ≤ b.val) (l : Fin (k + 1)) :
    pTop k r j q (wI k r l) (esI k r b) = q.1 ⟨b, hb⟩ l := by
  have h1 : (wI k r l).val = r + l.val := rfl
  have h2 : (esI k r b).val = 2 * r + k - b.val := rfl
  have := l.isLt
  have := b.isLt
  unfold pTop pOf pEl
  rw [if_neg (wI_ne_esI' l b), dite_eq_right (by omega), dif_pos (by omega)]
  have e1 : (⟨2 * r + k - (esI k r b).val, by omega⟩ : Fin r) = b := by
    apply Fin.ext
    show 2 * r + k - (2 * r + k - b.val) = b.val
    omega
  have e2 : (⟨(wI k r l).val - r, by omega⟩ : Fin (k + 1)) = l := by
    apply Fin.ext
    show r + l.val - r = l.val
    omega
  have hb' : j ≤ 2 * r + k - (esI k r b).val := by omega
  simp only [e1, e2, dif_pos hb']

private theorem crd_mulVec_bvec_eI_eq_upperIn {k r j : ℕ} (β : Fin r → ℕ) (q : (UTin β → ℂ) × PTop k r j) (a b : Fin r) :
    (crd k r j β q *ᵥ bvec (eI k r b)) (eI k r a) = upperIn β q.1 a b := by
  have ha : (eI k r a).val = a.val := rfl
  have hb : (eI k r b).val = b.val := rfl
  have := a.isLt
  have := b.isLt
  rw [crd, ← Matrix.mulVec_mulVec, pTop_mulVec_eq_of_vanishing, mulVec_bvec_lemma_2]
  · unfold uEmb
    rw [dif_pos (by omega)]
    rfl
  · intro m hm
    rw [mulVec_bvec_lemma_2]
    unfold uEmb
    have hne : m ≠ eI k r b := by
      intro h
      have := congrArg Fin.val h
      omega
    rw [dite_eq_right (by omega), dite_eq_right (by omega), if_neg hne]

theorem coords_top : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (r : ℕ) (N : NF H r) (k : ℕ) (σ : K →+* ℂ) (ρ : ℝ) (β : Fin r → ℕ) (Φ : V → Fin (2 * r + k + 1) → ℂ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r), 0 < ρ → IsFrameOf N k σ ρ β Φ z z' g → ∀ (s : V ≃ₗ[K] V) (q : (UTin β → ℂ) × PTop k r N.j), (∀ x, crd k r N.j β q *ᵥ Φ x = Φ (s x)) → (∀ (i : UTin β) (u : Fin r → K), s (N.F.e i.1.1.2.castSucc) = N.F.e i.1.1.2.castSucc + ∑ c, u c • N.F.e c.castSucc → q.1 i = ((ρ ^ (i.1.1.2.val - i.1.1.1.val) : ℝ) : ℂ) * σ (u i.1.1.1)) ∧ (q.1 = 0 → ∀ a : Fin r, s (N.F.e a.castSucc) = N.F.e a.castSucc) ∧ (q.1 = 0 → ∀ (b : {a : Fin r // N.j ≤ a.val}) (y : V), s (N.ist b.1) - N.ist b.1 - y ∈ II N.F N.F' → q.2.1 b = ((ρ ^ (r - b.1.val) : ℝ) : ℂ) • fun l => Φ y (wI k r l)) := by
  intro K V _ _ _ _ _ _ _ _ H r N k σ ρ β Φ z z' g hρ hF s q hq
  obtain ⟨hR, -, -, -, -, hE, hI, -, -⟩ := hF
  obtain ⟨hadd, hsmul, -, -⟩ := id hR
  have hv : ∀ a : Fin r, Φ (N.F.e a.castSucc) = ((ρ ^ (r - a.val) : ℝ) : ℂ) • bvec (eI k r a) :=
    fun a => (hE a).1
  have hρc : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨⟨⟨a, b⟩, hab⟩, hβ⟩ u hsu
    dsimp only at hab hβ hsu ⊢
    have hab' : a.val < b.val := hab
    have hcol : upperIn β q.1 a b = q.1 ⟨⟨(a, b), hab⟩, hβ⟩ := by
      simp [upperIn, upper, hab, hβ]
    have key := congrFun (hq (N.F.e b.castSucc)) (eI k r a)
    rw [hsu, hadd, RealMat.phi_sum hR, hv b, Matrix.mulVec_smul, Pi.smul_apply, crd_mulVec_bvec_eI_eq_upperIn, hcol] at key
    simp only [hsmul, hv, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, bvec, Pi.single_apply,
      eI_inj', hab.ne, if_false, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      zero_add, Complex.ofReal_pow] at key
    have hne : (ρ : ℂ) ^ (r - b.val) ≠ 0 := pow_ne_zero _ hρc
    have hpow : (ρ : ℂ) ^ (r - a.val) = (ρ : ℂ) ^ (r - b.val) * (ρ : ℂ) ^ (b.val - a.val) := by
      rw [← pow_add]
      congr 1
      have := b.isLt
      omega
    push_cast
    apply mul_left_cancel₀ hne
    linear_combination key + σ (u a) * hpow
  · intro h0 a
    apply RealMat.phi_inj hR
    rw [← hq, crd_of_zero β q h0, hv a, Matrix.mulVec_smul, pTop_mulVec_eq_of_vanishing]
    intro m hm
    simp only [bvec, Pi.single_apply]
    rw [if_neg]
    intro h
    have h1 := congrArg Fin.val h
    have h2 : (eI k r a).val = a.val := rfl
    have := a.isLt
    omega
  · rintro h0 ⟨b, hb⟩ y hy
    dsimp only at hy ⊢
    funext l
    have hw : s (N.ist b) - N.ist b - y ∈ N.F.Xa r := (Submodule.mem_inf.mp hy).1
    have hz := RealMat.coord_of_mem_Xa hR (fun a => (hE a).1) hw (wI k r l)
      (by have : (wI k r l).val = r + l.val := rfl; omega)
    have key := congrFun (hq (N.ist b)) (wI k r l)
    have hsplit : s (N.ist b) = N.ist b + y + (s (N.ist b) - N.ist b - y) := by abel
    rw [hsplit, hadd, hadd, hI b hb, crd_of_zero β q h0, Matrix.mulVec_smul, Pi.smul_apply, mulVec_bvec_lemma_2,
      pTop_wI_esI_eq q.2 b hb l] at key
    simp only [Pi.add_apply, hz, add_zero, Pi.smul_apply, bvec, Pi.single_apply, wI_ne_esI' l b, if_false,
      smul_eq_mul, mul_zero, zero_add, Complex.ofReal_inv, Complex.ofReal_pow] at key
    simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_pow]
    have hne : (ρ : ℂ) ^ (r - b.val) ≠ 0 := pow_ne_zero _ hρc
    rw [← key, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]

end GlobalTheory.DegVol.RefCovTop
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealFrameAutomorphismUnitriangularRowsCoordsStatement
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realFrame_automorphism_unitriangular_rows_coords : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (r : ℕ) (N : NF H r) (k : ℕ) (σ : K →+* ℂ) (ρ : ℝ) (β : Fin r → ℕ) (Φ : V → Fin (2 * r + k + 1) → ℂ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r), 0 < ρ → IsFrameOf N k σ ρ β Φ z z' g → ∀ (s : V ≃ₗ[K] V) (q : (UTin β → ℂ) × PTop k r N.j), (∀ x, crd k r N.j β q *ᵥ Φ x = Φ (s x)) → (∀ (i : UTin β) (u : Fin r → K), s (N.F.e i.1.1.2.castSucc) = N.F.e i.1.1.2.castSucc + ∑ c, u c • N.F.e c.castSucc → q.1 i = ((ρ ^ (i.1.1.2.val - i.1.1.1.val) : ℝ) : ℂ) * σ (u i.1.1.1)) ∧ (q.1 = 0 → ∀ a : Fin r, s (N.F.e a.castSucc) = N.F.e a.castSucc) ∧ (q.1 = 0 → ∀ (b : {a : Fin r // N.j ≤ a.val}) (y : V), s (N.ist b.1) - N.ist b.1 - y ∈ II N.F N.F' → q.2.1 b = ((ρ ^ (r - b.1.val) : ℝ) : ℂ) • fun l => Φ y (wI k r l)) := by
  first | exact @GlobalTheory.DegVol.RefCovTop.coords_top | exact GlobalTheory.DegVol.RefCovTop.coords_top | (intros; apply GlobalTheory.DegVol.RefCovTop.coords_top <;> assumption)
end
end
