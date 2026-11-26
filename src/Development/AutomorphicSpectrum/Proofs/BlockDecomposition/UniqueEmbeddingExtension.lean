module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.CalcSteps
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalCalculusCurve

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniqueEmbeddingExtension
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniqueEmbeddingExtension
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical

namespace GlobalTheory.CompanionTheory.EmbUniq

variable {l : ℕ} [Fact l.Prime]

theorem norm_coe_algHom {K L : FinExt l} (τ : ↥K.1 →ₐ[ℚ_[l]] ↥L.1) (x : ↥K.1) :
    ‖((τ x : ↥L.1) : Om l)‖ = ‖(x : Om l)‖ := by
  have a := minpoly.algHom_eq (L.1.val.comp τ) (RingHom.injective (L.1.val.comp τ : ↥K.1 →+* Om l)) x
  have b := minpoly.algHom_eq K.1.val (RingHom.injective (K.1.val : ↥K.1 →+* Om l)) x
  have c : minpoly ℚ_[l] ((τ x : ↥L.1) : Om l) = minpoly ℚ_[l] (x : Om l) := a.trans b.symm
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm, c]

theorem norm_le_one_of_isIntegral {x : Om l} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h1 : IsIntegral (NormedField.valuation (K := Om l)).integer x := hx.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := Om l))).mem_of_integral h1
  have h3 : ‖x‖₊ ≤ 1 := h2
  exact_mod_cast h3

variable {E : Type} [Field E] [NumberField E]

theorem continuous_withVal (w : HeightOneSpectrum (𝓞 E)) (f : E →+* Om l)
    (h1 : ∀ x, w.valuation E x ≤ 1 → ‖f x‖ ≤ 1) (y : E) (hy0 : y ≠ 0) (hy : ‖f y‖ < 1) :
    Continuous (f.comp (WithVal.equiv (w.valuation E)).toRingHom) := by
  refine continuous_of_continuousAt_zero _ ?_
  rw [ContinuousAt, map_zero, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hy
  let x0 : WithVal (w.valuation E) := WithVal.toVal _ (y ^ n)
  have hx0' : x0 ≠ 0 := by
    intro h
    exact pow_ne_zero n hy0 ((WithVal.equiv (w.valuation E)).symm.map_eq_zero_iff.1 h)
  have h0 : Valued.v.restrict x0 ≠ 0 := by simp [hx0']
  filter_upwards [Valued.mem_nhds_zero.2 ⟨Units.mk0 _ h0, subset_rfl⟩] with z hz
  simp only [Set.mem_setOf_eq, Units.val_mk0, Valuation.restrict_lt_iff] at hz
  have hz' : w.valuation E (WithVal.equiv (w.valuation E) z) < w.valuation E (y ^ n) := hz
  have hv : 0 < w.valuation E (y ^ n) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (pow_ne_zero n hy0))
  have hu : w.valuation E (WithVal.equiv (w.valuation E) z / y ^ n) ≤ 1 := by
    rw [map_div₀]
    exact (div_le_one₀ hv).2 hz'.le
  have h2 := h1 _ hu
  have hp : 0 < ‖f y‖ ^ n := pow_pos (norm_pos_iff.2 ((map_ne_zero f).2 hy0)) n
  rw [map_div₀, map_pow, norm_div, norm_pow, div_le_one₀ hp] at h2
  rw [dist_zero_right]
  exact lt_of_le_of_lt h2 hn

def toKw {Ω : Type} [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) : E →+* ↥Bw.Kw.1 :=
  (Bw.j.comp (algebraMap E Ω)).codRestrict Bw.Kw.1 Bw.j_E

theorem existsUnique_continuous_induced : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw → ∀ (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1),
      ∃! j : {j : w.adicCompletion E →+* Qbar l // Continuous j},
        IsInduced Bw (j.1.comp (algebraMap E (w.adicCompletion E))) τ' := by
  intro E Ω _ _ _ _ _ l _ w A hA O _ _ _ Bw hj LL' τ'
  let g : E →+* ↥LL'.1 := (τ' : ↥Bw.Kw.1 →+* ↥LL'.1).comp (toKw Bw)
  let f : E →+* Om l := (algebraMap ↥LL'.1 (Om l)).comp g
  have hfn : ∀ x, ‖f x‖ = ‖Bw.j (algebraMap E Ω x)‖ := fun x => norm_coe_algHom τ' (toKw Bw x)
  have hlt : ∀ y : 𝓞 E, ‖f (y : E)‖ < 1 ↔ y ∈ w.asIdeal := fun y => by
    rw [hfn, ← hj.valuation_lt_one_iff]
    exact hA y
  have hint : ∀ y : 𝓞 E, ‖f (y : E)‖ ≤ 1 := fun y =>
    norm_le_one_of_isIntegral (by
      convert map_isIntegral_int f (RingOfIntegers.isIntegral_coe y)
      exact Subsingleton.elim _ _)
  have h1 : ∀ x, w.valuation E x ≤ 1 → ‖f x‖ ≤ 1 := fun x hx => by
    obtain ⟨n, d, h⟩ := w.exists_primeCompl_mul_eq_of_integer x hx
    have hd : 1 ≤ ‖f ((d : 𝓞 E) : E)‖ := not_lt.1 fun hl => d.2 ((hlt _).1 hl)
    have h2 : ‖f x‖ * ‖f ((d : 𝓞 E) : E)‖ = ‖f (n : E)‖ := by
      rw [← norm_mul, ← map_mul]
      exact congrArg (fun z => ‖f z‖) h
    have h3 := hint n
    nlinarith [norm_nonneg (f x)]
  obtain ⟨y, hyw, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
  have hc := continuous_withVal w f h1 (y : E) (by simpa using hy0) ((hlt y).2 hyw)
  have hcg : Continuous (g.comp (WithVal.equiv (w.valuation E)).toRingHom) :=
    Topology.IsInducing.subtypeVal.continuous_iff.2 hc
  haveI : FiniteDimensional ℚ_[l] ↥LL'.1 := LL'.2
  haveI : CompleteSpace ↥LL'.1 := FiniteDimensional.complete ℚ_[l] ↥LL'.1
  let ext : w.adicCompletion E →+* ↥LL'.1 :=
    (UniformSpace.Completion.extensionHom _ hcg).comp (HeightOneSpectrum.adicCompletion.equiv E w).toRingHom
  have hextc : Continuous ext := UniformSpace.Completion.continuous_extension.comp
    (HeightOneSpectrum.adicCompletion.continuous_toCompletion E w)
  have hext : ∀ x : E, ext (algebraMap E _ x) = g x := fun k =>
    UniformSpace.Completion.extensionHom_coe _ hcg (WithVal.toVal _ k)
  have hval : ∀ x : E, ((ext (algebraMap E _ x) : ↥LL'.1) : Om l) = f x := fun x =>
    congrArg (Subtype.val) (hext x)
  refine ⟨⟨(algebraMap ↥LL'.1 (Om l)).comp ext, continuous_subtype_val.comp hextc⟩, fun x => (hval x), ?_⟩
  rintro ⟨j', hj'c⟩ hj'
  refine Subtype.ext (DFunLike.coe_injective ((HeightOneSpectrum.denseRange_algebraMap E w).equalizer hj'c
    (continuous_subtype_val.comp hextc) (funext fun x => ?_)))
  exact (hj' x).trans (hval x).symm

end GlobalTheory.CompanionTheory.EmbUniq
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniqueEmbeddingExtensionStatement
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unique_embedding_extension : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw → ∀ (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1),
      ∃! j : {j : w.adicCompletion E →+* Qbar l // Continuous j},
        IsInduced Bw (j.1.comp (algebraMap E (w.adicCompletion E))) τ' := by
  first | exact @GlobalTheory.CompanionTheory.EmbUniq.existsUnique_continuous_induced | exact GlobalTheory.CompanionTheory.EmbUniq.existsUnique_continuous_induced | (intros; apply GlobalTheory.CompanionTheory.EmbUniq.existsUnique_continuous_induced <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PaleyWienerDecay
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PaleyWienerDecay
noncomputable section

open MeasureTheory Filter Topology
open scoped ZeroAtInfty ContDiff

namespace GlobalTheory.CompanionTheory.WaveCurve.Decay

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.WaveCurve

def ct (φ : ℝ → ℝ) (y : ℝ) : ℂ := ∫ t, (φ t : ℂ) * chj 0 t y

def Tst (φ : ℝ → ℝ) : Prop := ContDiff ℝ ∞ φ ∧ HasCompactSupport φ

lemma Tst.deriv {φ : ℝ → ℝ} (h : Tst φ) : Tst (deriv φ) :=
  ⟨(contDiff_infty_iff_deriv.1 h.1).2, h.2.deriv⟩

lemma Tst.cont {φ : ℝ → ℝ} (h : Tst φ) : Continuous fun t => (φ t : ℂ) :=
  Complex.continuous_ofReal.comp h.1.continuous

lemma Tst.cs {φ : ℝ → ℝ} (h : Tst φ) : HasCompactSupport fun t => (φ t : ℂ) :=
  h.2.comp_left Complex.ofReal_zero

lemma chj_add_two (j : ℕ) (t y : ℝ) : chj (j + 2) t y = (y : ℂ) * chj j t y := by
  have h : ((y : ℂ) ^ (1 / 2 : ℂ)) ^ 2 = (y : ℂ) := by
    simp [one_div]
  have hp : Even (j + 2) ↔ Even j := by simp [Nat.even_add]
  unfold chj
  simp only [hp, pow_add, h]
  ring

lemma chj_zero (t y : ℝ) : chj 0 t y = Complex.cosh ((t : ℂ) * (y : ℂ) ^ (1 / 2 : ℂ)) := by
  simp [chj]

lemma chj_cont (j : ℕ) (y : ℝ) : Continuous fun t => chj j t y :=
  continuous_iff_continuousAt.2 fun t => (chj_hasDerivAt j t y).continuousAt

lemma ibp {φ : ℝ → ℝ} (h : Tst φ) (j : ℕ) (y : ℝ) :
    ∫ t, (φ t : ℂ) * chj (j + 1) t y = - ∫ t, ((deriv φ t : ℝ) : ℂ) * chj j t y := by
  have hd : ∀ t, HasDerivAt (fun t => (φ t : ℂ)) ((deriv φ t : ℝ) : ℂ) t := fun t =>
    ((h.1.differentiable (by simp)) t).hasDerivAt.ofReal_comp
  have i : ∀ (ψ : ℝ → ℝ), Tst ψ → ∀ k : ℕ,
      Integrable ((fun t => (ψ t : ℂ)) * (fun t => chj k t y)) := fun ψ hψ k =>
    (hψ.cont.mul (chj_cont k y)).integrable_of_hasCompactSupport hψ.cs.mul_right
  exact integral_mul_deriv_eq_deriv_mul_of_integrable (fun t _ => hd t)
    (fun t _ => chj_hasDerivAt j t y) (i φ h (j + 1)) (i _ h.deriv j) (i φ h j)

lemma ct_two {φ : ℝ → ℝ} (h : Tst φ) (y : ℝ) :
    (y : ℂ) * ct φ y = ct (deriv (deriv φ)) y := by
  unfold ct
  rw [← integral_const_mul]
  have e : ∀ t, (y : ℂ) * ((φ t : ℂ) * chj 0 t y) = (φ t : ℂ) * chj (1 + 1) t y := by
    intro t
    rw [show chj (1 + 1) t y = chj (0 + 2) t y from rfl, chj_add_two 0]
    ring
  simp_rw [e]
  rw [ibp h 1 y, ibp h.deriv 0 y, neg_neg]

lemma ct_pow (m : ℕ) {φ : ℝ → ℝ} (h : Tst φ) :
    ∃ ψ, Tst ψ ∧ ∀ y : ℝ, (y : ℂ) ^ m * ct φ y = ct ψ y := by
  induction m with
  | zero => exact ⟨φ, h, fun y => by simp⟩
  | succ m ih =>
    obtain ⟨ψ, hψ, e⟩ := ih
    refine ⟨deriv (deriv ψ), hψ.deriv.deriv, fun y => ?_⟩
    rw [← ct_two hψ, ← e, pow_succ]
    ring

lemma ct_continuous {φ : ℝ → ℝ} (h : Tst φ) : Continuous (ct φ) := by
  have hc : Continuous fun p : ℝ × ℝ => chj 0 p.2 p.1 := by
    have hs : Continuous fun y : ℝ => (y : ℂ) ^ (1 / 2 : ℂ) :=
      Complex.continuous_ofReal_cpow_const (by norm_num [Complex.div_re])
    simp only [chj_zero]
    exact Complex.continuous_cosh.comp ((Complex.continuous_ofReal.comp continuous_snd).mul
      (hs.comp continuous_fst))
  have hf : Continuous (Function.uncurry fun (y t : ℝ) => (φ t : ℂ) * chj 0 t y) :=
    (h.cont.comp continuous_snd).mul hc
  have := continuous_parametric_integral_of_continuous (μ := volume) hf h.2
  convert this using 2 with y
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => ?_).symm
  simp [image_eq_zero_of_notMem_tsupport ht]

lemma ct_bound (c : ℝ) {φ : ℝ → ℝ} (h : Tst φ) :
    ∃ B : ℝ, ∀ y, ‖(cut c y : ℂ) * ct φ y‖ ≤ B := by
  set A := Real.sqrt (max (c + 1) 0) with hA
  have hi : Integrable fun t => ‖(φ t : ℂ)‖ * Real.exp (|t| * A) :=
    (h.cont.norm.mul (by fun_prop)).integrable_of_hasCompactSupport h.cs.norm.mul_right
  refine ⟨∫ t, ‖(φ t : ℂ)‖ * Real.exp (|t| * A), fun y => ?_⟩
  have hB : 0 ≤ ∫ t, ‖(φ t : ℂ)‖ * Real.exp (|t| * A) :=
    integral_nonneg fun t => by positivity
  rcases le_or_gt (c + 1) y with hy | hy
  · simpa [cut_eq_zero hy] using hB
  · have h1 : ‖ct φ y‖ ≤ ∫ t, ‖(φ t : ℂ)‖ * Real.exp (|t| * A) := by
      refine norm_integral_le_of_norm_le hi (Eventually.of_forall fun t => ?_)
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [chj_zero]
      set z : ℂ := (t : ℂ) * (y : ℂ) ^ (1 / 2 : ℂ) with hz_def
      have hre : ((y : ℂ) ^ (1 / 2 : ℂ)).re = Real.sqrt (max y 0) := by
        have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
        rw [hhalf]
        rcases le_or_gt 0 y with hy | hy
        · rw [max_eq_left hy, Real.sqrt_eq_rpow, ← Complex.ofReal_cpow hy, Complex.ofReal_re]
        · rw [max_eq_right hy.le, Real.sqrt_zero, Complex.cpow_ofReal,
            Complex.arg_ofReal_of_neg hy, show Real.pi * (1 / 2 : ℝ) = Real.pi / 2 by ring]
          simp [Complex.mul_re]
      have hz : |z.re| = |t| * Real.sqrt (max y 0) := by
        rw [hz_def, Complex.re_ofReal_mul, hre, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      have h2 : ‖Complex.cosh z‖ ≤ Real.exp |z.re| := by
        have hcosh : Complex.cosh z = (Complex.exp z + Complex.exp (-z)) / 2 := by
          rw [← Complex.two_cosh]
          ring
        rw [hcosh, norm_div, Complex.norm_ofNat]
        have hsum := norm_add_le (Complex.exp z) (Complex.exp (-z))
        rw [Complex.norm_exp, Complex.norm_exp, Complex.neg_re] at hsum
        linarith [Real.exp_le_exp.mpr (le_abs_self z.re),
          Real.exp_le_exp.mpr (neg_le_abs z.re)]
      rw [hz] at h2
      refine h2.trans (Real.exp_le_exp.2 ?_)
      exact mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (max_le_max_right _ hy.le)) (abs_nonneg _)
    have h3 : ‖(cut c y : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (cut_nonneg c y)]
      exact cut_le_one c y
    rw [norm_mul]
    calc _ ≤ 1 * ∫ t, ‖(φ t : ℂ)‖ * Real.exp (|t| * A) :=
          mul_le_mul h3 h1 (norm_nonneg _) zero_le_one
      _ = _ := one_mul _

lemma tst_of_bump {g : ℝ → ℝ} {T : ℝ} (hb : IsBump g T) : Tst g := by
  refine ⟨hb.1, HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) T) fun t ht => ?_⟩
  refine hb.2.2 t ?_
  simpa [Real.norm_eq_abs] using ht

lemma hg_pow {g : ℝ → ℝ} (h : Tst g) (c : ℝ) (m : ℕ) :
    ∃ ψ, Tst ψ ∧ ∀ y : ℝ, (y : ℂ) ^ m * hg c g y = (cut c y : ℂ) * ct ψ y := by
  obtain ⟨ψ, hψ, e⟩ := ct_pow m h
  refine ⟨ψ, hψ, fun y => ?_⟩
  rw [← e]
  show (y : ℂ) ^ m * ((cut c y : ℂ) * ct g y) = _
  ring

lemma hg_continuous {g : ℝ → ℝ} (h : Tst g) (c : ℝ) (m : ℕ) :
    Continuous fun y : ℝ => (y : ℂ) ^ m * hg c g y := by
  obtain ⟨ψ, hψ, e⟩ := hg_pow h c m
  simp only [e]
  exact (Complex.continuous_ofReal.comp (cut_continuous c)).mul (ct_continuous hψ)

lemma hg_tendsto {g : ℝ → ℝ} (h : Tst g) (c : ℝ) (m : ℕ) :
    Tendsto (fun y : ℝ => (y : ℂ) ^ m * hg c g y) (cocompact ℝ) (𝓝 0) := by
  obtain ⟨ψ, hψ, e⟩ := hg_pow h c (m + 1)
  obtain ⟨B, hB⟩ := ct_bound c hψ
  have hn : Tendsto (fun y : ℝ => ‖y‖) (cocompact ℝ) atTop := tendsto_norm_cocompact_atTop
  refine squeeze_zero_norm' (a := fun y : ℝ => B * ‖y‖⁻¹) ?_ ?_
  · filter_upwards [hn.eventually_gt_atTop 0] with y hy
    rw [← div_eq_mul_inv, le_div_iff₀ hy]
    have h1 := hB y
    have h2 : (y : ℂ) ^ m * (y : ℂ) * hg c g y = ((y : ℂ) ^ m * hg c g y) * (y : ℂ) := by ring
    rw [← e, pow_succ, h2, norm_mul, Complex.norm_real] at h1
    exact h1
  · simpa using (tendsto_inv_atTop_zero.comp hn).const_mul B

def ev (y : ℝ) : C₀(ℝ, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => f y, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl } 1
    (fun f => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
      exact f.toBCF.norm_coe_le_norm y)

lemma ev_apply (y : ℝ) (f : C₀(ℝ, ℂ)) : ev y f = f y := rfl

theorem pwdecay : PWdecay := by
  intro c g T hb
  have hT := tst_of_bump hb
  refine ⟨fun m => ⟨hg_continuous hT c m, hg_tendsto hT c m⟩, fun N hN => ?_⟩
  set R : ℝ → ℂ := fun y => ((((1 + y ^ 2) ^ N)⁻¹ : ℝ) : ℂ) * hg c g y with hR
  have hW : Continuous fun y : ℝ => ((((1 + y ^ 2) ^ N)⁻¹ : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (Continuous.inv₀ (by fun_prop) fun y => by positivity)
  have hg0 := hg_continuous hT c 0
  have ht0 := hg_tendsto hT c 0
  simp only [pow_zero, one_mul] at hg0 ht0
  have hRc : Continuous R := hW.mul hg0
  have hRt : Tendsto R (cocompact ℝ) (𝓝 0) := by
    refine squeeze_zero_norm (a := fun y => ‖hg c g y‖) (fun y => ?_) (by simpa using ht0.norm)
    rw [hR, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 : |((1 + y ^ 2) ^ N)⁻¹| ≤ 1 := by
      rw [abs_of_nonneg (by positivity)]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by nlinarith [sq_nonneg y]))
    exact mul_le_of_le_one_left (norm_nonneg _) h1
  have hF : Continuous fun t => toC0 (wv c N 0 t) :=
    continuous_iff_continuousAt.2 fun t => (fcurve c N 0 (by omega) t).2.continuousAt
  have hH : Integrable fun t => (g t : ℂ) • toC0 (wv c N 0 t) :=
    (hT.cont.smul hF).integrable_of_hasCompactSupport hT.cs.smul_right
  ext y
  rw [coe_toC0 hRc hRt, ← ev_apply y, ← (ev y).integral_comp_comm hH]
  have e : ∀ t, ev y ((g t : ℂ) • toC0 (wv c N 0 t)) =
      ((cut c y * ((1 + y ^ 2) ^ N)⁻¹ : ℝ) : ℂ) * ((g t : ℂ) * chj 0 t y) := by
    intro t
    have h1 := (fcurve c N 0 (by omega) t).1
    rw [map_smul, ev_apply, coe_toC0 h1.1 h1.2, smul_eq_mul]
    unfold wv
    ring
  simp_rw [e]
  rw [integral_const_mul, hR]
  show _ = _ * ((cut c y : ℂ) * ct g y)
  unfold ct
  push_cast
  ring

end GlobalTheory.CompanionTheory.WaveCurve.Decay
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PaleyWienerDecayStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.paley_wiener_decay : PositivityTheory.RgBcC.Fc.PWdecay := by
  first | exact @GlobalTheory.CompanionTheory.WaveCurve.Decay.pwdecay | exact GlobalTheory.CompanionTheory.WaveCurve.Decay.pwdecay | (intros; apply GlobalTheory.CompanionTheory.WaveCurve.Decay.pwdecay <;> assumption)
end
end
