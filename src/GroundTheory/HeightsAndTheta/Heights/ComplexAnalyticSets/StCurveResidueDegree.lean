module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Assembly
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartHomogenise

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveResidueDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def CurveResidueDegree.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ),
    IsRadicalAt I q → ringKrullDim (curveLocalRing I q) = 1 →
      ∀ P : MaximalSpectrum (curveNormalisation I q),
        Module.length (curveLocalRing I q) (curveNormalisation I q ⧸ P.asIdeal) = 1

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PVarIntAdd
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

noncomputable section

namespace VarIntAdd

theorem ringKrullDim_eq_of_injective_finite {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hinj : Function.Injective f) (hfin : f.Finite) : ringKrullDim S = ringKrullDim R := by
  let : Algebra R S := f.toAlgebra
  have : Algebra.IsIntegral R S := ⟨hfin.to_isIntegral⟩
  apply le_antisymm
  · have hg : StrictMono (PrimeSpectrum.comap (algebraMap R S)) := by
      intro q₁ q₂ hq
      have hlt : q₁.asIdeal < q₂.asIdeal := hq
      obtain ⟨hle, x, hx2, hx1⟩ := SetLike.lt_iff_le_and_exists.mp hlt
      show q₁.asIdeal.comap (algebraMap R S) < q₂.asIdeal.comap (algebraMap R S)
      exact Ideal.comap_lt_comap_of_integral_mem_sdiff hle ⟨hx2, hx1⟩
        (Algebra.IsIntegral.isIntegral x)
    exact Order.krullDim_le_of_strictMono _ hg
  · refine iSup_le fun l => ?_
    have hker : (⊥ : Ideal S).comap (algebraMap R S) ≤ (RelSeries.head l).asIdeal := by
      intro r hr
      have : f r = 0 := hr
      rw [show r = 0 from hinj (by rw [this, map_zero])]
      exact Ideal.zero_mem _
    obtain ⟨P, -, hP, hPo⟩ := Ideal.exists_ideal_over_prime_of_isIntegral _ ⊥ hker
    have : P.LiesOver (RelSeries.head l).asIdeal := ⟨hPo.symm⟩
    obtain ⟨L, hlen, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
    exact le_iSup_of_le L (by rw [hlen])

theorem ringKrullDim_of_isFiniteProjection {n k : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin k) (Fin n) ℂ} (hA : IsFiniteProjection J A) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = k := by
  rw [ringKrullDim_eq_of_injective_finite (projHom J A).toRingHom hA.injective hA.finite,
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

theorem chartDens_add {n k : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin k) (Fin n) ℂ}
    (hfin : ∀ y, (ComplexSets.fibre J A y).Finite) (f g : (Fin n → ℂ) → ℝ) (φ : Fin k → (Fin n → ℂ) → ℝ) :
    chartDens J A (f + g) φ = chartDens J A f φ + chartDens J A g φ := by
  funext y
  simp only [chartDens, sheetSum, Pi.add_apply]
  rw [← finsum_mem_add_distrib (hfin y)]
  refine finsum_mem_congr rfl fun x _ => ?_
  split_ifs <;> ring

theorem abs_chartDens_le {n k : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin k) (Fin n) ℂ}
    (hfin : ∀ y, (ComplexSets.fibre J A y).Finite) (w : (Fin n → ℂ) → ℝ) (φ : Fin k → (Fin n → ℂ) → ℝ)
    (y : Fin k → ℂ) : |chartDens J A w φ y| ≤ chartAbsDens J A w φ y := by
  simp only [chartDens, chartAbsDens, sheetSum]
  rw [finsum_mem_eq_finite_toFinset_sum _ (hfin y), finsum_mem_eq_finite_toFinset_sum _ (hfin y)]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun x _ => ?_))
  split_ifs <;> simp

end VarIntAdd

theorem VarIntAdd.proof (hCM : ChartMassCompact.Statement) : VarIntAdd.Statement := by
  intro n k J f g φ hJ hfc hfs hgc hgs hφ
  unfold varInt
  split_ifs with h
  · set A := h.choose
    have hA : IsFiniteProjection J A := h.choose_spec
    have hd := VarIntAdd.ringKrullDim_of_isFiniteProjection hA
    have hfin : ∀ y, (ComplexSets.fibre J A y).Finite := fun y => (FibreBound.proof n k J A hJ hd hA y).2.1
    have hint : ∀ w : (Fin n → ℂ) → ℝ, Continuous w → HasCompactSupport w →
        Integrable (chartDens J A w φ) := by
      intro w hwc hws
      have hm := SheetSumMeasurable.proof n k J A w φ hJ hd hA hwc.measurable hφ
      refine (hCM n k J A w φ hJ hd hA hwc.continuousOn hφ (Or.inl hws)).mono'
        hm.1.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs]
      exact VarIntAdd.abs_chartDens_le hfin w φ y
    unfold chartInt
    rw [VarIntAdd.chartDens_add hfin, integral_add' (hint f hfc hfs) (hint g hgc hgs)]
  · simp

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalCurvePointDVR
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def NormalCurvePointDVR.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) →
    ringKrullDim (MvPolynomial σ ℂ ⧸ I) = (1 : ℕ) → w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn I →
      ∃ _ : IsDomain (pointLocalRing I w), IsDiscreteValuationRing (pointLocalRing I w)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMLengthParameters
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing

universe u

noncomputable section

def CMLengthParameters.Statement : Prop :=
  ∀ (B : Type u) [CommRing B] [IsCohenMacaulayLocalRing B] (P : Ideal B) [P.IsPrime] (d : ℕ) (x : Fin d → B),
    minimalPrimes B = {P} → ringKrullDim (B ⧸ P) = (d : ℕ) →
    Ideal.span (Set.range x) ⊔ P = maximalIdeal B →
      Module.length B (B ⧸ Ideal.span (Set.range x)) =
        Module.length (Localization.AtPrime P) (Localization.AtPrime P)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalCurveBranchOrder
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def NormalCurveBranchOrder.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    (w : Fin n ⊕ Fin M.m → ℂ) (r : ℝ) (φ : (Fin 1 → ℂ) → Fin n ⊕ Fin M.m → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (1 : ℕ) → 0 < r →
    DifferentiableOn ℂ φ (Metric.ball 0 r) → Set.InjOn φ (Metric.ball 0 r) →
    Set.MapsTo φ (Metric.ball 0 r) (IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal) → φ 0 = w →
      ∀ g : MvPolynomial (Fin n ⊕ Fin M.m) ℂ,
        Ring.ord (pointLocalRing M.ideal w)
            (algebraMap (MvPolynomial (Fin n ⊕ Fin M.m) ℂ) (pointLocalRing M.ideal w) g) =
          analyticOrderAt (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) g) 0

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOffTube
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Matrix ComplexSets

noncomputable section

theorem measurable_tubeWeight {m : ℕ} (Q : MvPolynomial (Fin m) ℂ) : Measurable (tubeWeight Q) := by
  have hl : Measurable (logAbsSq Q) :=
    Real.measurable_log.comp ((MvPolynomial.continuous_eval Q).norm.pow 2).measurable
  exact Measurable.ite (measurableSet_le hl measurable_const) ((hl.pow_const 2).inv) measurable_const

theorem measurable_tubeDens {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin (d + 1)) (Fin n) ℂ} (hA : IsFiniteProjection J A) (P : MvPolynomial (Fin (d + 1)) ℂ)
    (R : ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) : Measurable (tubeDens J A P R φ) := by
  have hAm : Measurable fun x : Fin n → ℂ => A *ᵥ x :=
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)).continuous.measurable
  have hw : Measurable ((Metric.closedBall (0 : Fin n → ℂ) R).indicator
      fun x => tubeWeight P (A *ᵥ x)) :=
    ((measurable_tubeWeight P).comp hAm).indicator measurableSet_closedBall
  exact SheetSumMeasurable.measurable_sheetSum hA (fun a b => |a * b|)
    (continuous_abs.comp continuous_mul).measurable hw _

theorem tubeDens_nonneg {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ))
    (A : Matrix (Fin (d + 1)) (Fin n) ℂ) (P : MvPolynomial (Fin (d + 1)) ℂ) (R : ℝ)
    (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin (d + 1) → ℂ) : 0 ≤ tubeDens J A P R φ y :=
  finsum_nonneg fun _ => finsum_nonneg fun _ => by split_ifs <;> positivity

theorem CutOffTube.proof (hC : TubeFormCompare.Statement) (hE : TubeEuclMass.Statement) :
    CutOffTube.Statement := by
  intro n d J A P R φ hJ hdim hA hP hφ
  obtain ⟨C, hCle⟩ := hC n d J A P R φ hJ hdim hA hφ
  refine Integrable.mono' ((hE n d J A P R hJ hdim hA hP).const_mul C)
    (measurable_tubeDens hA P R φ).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (tubeDens_nonneg J A P R φ y)]
  exact hCle y

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.MeasurableOfContinuousOnNeZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial MeasureTheory Filter Topology Matrix

noncomputable section

theorem le_ringKrullDim_slice {n e : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {ℓ : Fin n → ℂ}
    (hJ : IsAffVariety J (e + 1)) (hH : IsHomogIdeal J) (hℓ : linForm ℓ ∉ J) :
    ((e : ℕ) : WithBot ℕ∞) ≤
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {linForm ℓ - 1})) := by
  have hP := hJ.isPrime
  have hne : J ⊔ Ideal.span {linForm ℓ - 1} ≠ ⊤ := by
    intro htop
    have h1 : (1 : MvPolynomial (Fin n) ℂ) ∈ J :=
      GroundTheory.Heights₂.Heights.ChartDehomog.proof ℂ n J ℓ 1 0 hP hH hℓ (isHomogeneous_one _ _)
        (htop ▸ Submodule.mem_top)
    exact hP.ne_top ((Ideal.eq_top_iff_one J).mpr h1)
  obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes hne
  have hpP : p.IsPrime := hp.1.1
  have hJp : J ≤ p := le_sup_left.trans hp.1.2
  have hht := Ideal.map_height_le_one_of_mem_minimalPrimes hp
  have hpm : (p.map (Ideal.Quotient.mk J)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hform := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient (k := ℂ)
    (p.map (Ideal.Quotient.mk J))
  rw [hJ.dim, ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hJp)] at hform
  have hle : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ p) ≤
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {linForm ℓ - 1})) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor hp.1.2)
      (Ideal.Quotient.factor_surjective hp.1.2)
  refine le_trans ?_ hle
  have key : ∀ a b : ℕ∞, a ≤ 1 → a + b = ((e + 1 : ℕ) : ℕ∞) → (e : ℕ∞) ≤ b := by
    intro a b ha hab
    induction b using ENat.recTopCoe with
    | top => exact le_top
    | coe m =>
      induction a using ENat.recTopCoe with
      | top => simp at ha
      | coe k =>
        have h1 : k ≤ 1 := by exact_mod_cast ha
        have h2 : k + m = e + 1 := by exact_mod_cast hab
        exact_mod_cast (by omega : e ≤ m)
  generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ p) = D at hform ⊢
  induction D using WithBot.recBotCoe with
  | bot =>
    exfalso
    rw [WithBot.add_bot] at hform
    exact WithBot.bot_ne_coe hform
  | coe b =>
    have hab : (p.map (Ideal.Quotient.mk J)).height + b = ((e + 1 : ℕ) : ℕ∞) := by
      exact_mod_cast hform
    exact_mod_cast key _ b hht hab

theorem exists_isChowForm_iff {n e : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (hJ : IsProjPrime J) :
    (∃ F : MvPolynomial (Fin (e + 1) × Fin n) ℂ, IsChowForm J (e + 1) F) ↔
      IsAffVariety J (e + 1) :=
  ⟨fun ⟨F, hF⟩ => ⟨hJ.isPrime, GroundTheory.Heights₂.Heights.ConeDimOfChowForm.of_affineChartTrdeg
      GroundTheory.Heights₂.Heights.AffineChartTrdeg.proof ℂ n (e + 1) J F hJ hF⟩,
    fun hA => GroundTheory.Heights₂.Heights.ChowFormExists.of_affineChartTrdeg
      GroundTheory.Heights₂.Heights.AffineChartTrdeg.proof ℂ n (e + 1) J hJ hA.dim⟩

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOffDominated
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

namespace CutOffDominated

variable {n d : ℕ}

theorem chartDens_congr_zeroSet {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {f g : (Fin n → ℂ) → ℝ} (h : ∀ x ∈ zeroSet J, f x = g x) (φ : Fin d → (Fin n → ℂ) → ℝ) :
    chartDens J A f φ = chartDens J A g φ := by
  funext y
  unfold chartDens sheetSum
  refine finsum_congr fun x => finsum_congr fun hx => ?_
  simp only [h x hx.1]


open Classical in
theorem sheetSum_eq_sum {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (F : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ) {y : Fin d → ℂ} (hfin : (ComplexSets.fibre J A y).Finite) :
    sheetSum J A F y =
      ∑ x ∈ hfin.toFinset, if h : ∃ s, IsSheetAt J A x s then F x h.choose else 0 :=
  finsum_mem_eq_finite_toFinset_sum _ hfin

theorem ae_eval_ne_zero {ι : Type*} [Fintype ι] (g : MvPolynomial ι ℂ) (hg : g ≠ 0) :
    ∀ᵐ u : ι → ℂ, eval u g ≠ 0 := by
  have hU : (⋃ r : ℕ, LogInt.polydisc ι r) = Set.univ := by
    refine Set.eq_univ_of_forall fun u => ?_
    obtain ⟨r, hr⟩ := exists_nat_ge ‖u‖
    refine Set.mem_iUnion.mpr ⟨r, Set.mem_univ_pi.mpr fun i => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_le_pi_norm u i).trans hr
  have h := (ae_restrict_iUnion_iff (fun r : ℕ => LogInt.polydisc ι r) (fun u => eval u g ≠ 0)).mpr
    fun r => LogInt.ae_eval_ne_zero g hg r
  rwa [hU, Measure.restrict_univ] at h

end CutOffDominated

theorem CutOffDominated.proof : CutOffDominated.Statement := by
  classical
  intro n d J A P χ f ψ hJ hdim hA hP hχm hχ01 hlim hf hψ hint
  have hfin : ∀ y, (ComplexSets.fibre J A y).Finite := fun y =>
    (ComplexSets.FibreBound.proof n d J A hJ hdim hA y).2.1
  set g : (Fin n → ℂ) → ℝ := (zeroSet J).piecewise f 0 with hgdef
  have hg : Measurable g :=
    hf.measurable_piecewise continuousOn_const (SheetSumMeasurable.isClosed_zeroSet J).measurableSet
  have hmeas : ∀ k, Measurable (chartDens J A (fun x => χ k x * f x) ψ) := fun k => by
    rw [CutOffDominated.chartDens_congr_zeroSet (g := fun x => χ k x * g x)
      (fun x hx => by rw [hgdef, Set.piecewise_eq_of_mem _ _ _ hx])]
    exact (SheetSumMeasurable.proof n d J A _ ψ hJ hdim hA ((hχm k).mul hg) hψ).1
  refine tendsto_integral_of_dominated_convergence (chartAbsDens J A f ψ)
    (fun k => (hmeas k).aestronglyMeasurable) hint (fun k => Eventually.of_forall fun y => ?_) ?_
  · rw [Real.norm_eq_abs]
    unfold chartDens chartAbsDens
    rw [CutOffDominated.sheetSum_eq_sum _ (hfin y), CutOffDominated.sheetSum_eq_sum _ (hfin y)]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    split_ifs with h
    · rw [mul_assoc, abs_mul, abs_of_nonneg (hχ01 k x).1]
      exact mul_le_of_le_one_left (abs_nonneg _) (hχ01 k x).2
    · simp
  · filter_upwards [CutOffDominated.ae_eval_ne_zero P hP] with y hy
    unfold chartDens
    simp only [CutOffDominated.sheetSum_eq_sum _ (hfin y)]
    refine tendsto_finsetSum _ fun x hx => ?_
    rw [Set.Finite.mem_toFinset] at hx
    have hxl := hlim x hx.1 (by rw [show A *ᵥ x = y from hx.2]; exact hy)
    split_ifs with h
    · simpa using (hxl.mul_const (f x)).mul_const
        (ReciprocityTheory.AnForm.maDens (fun k => ψ k ∘ h.choose) y)
    · exact tendsto_const_nhds

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIntegralIndependent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

noncomputable section

namespace IntegralIndep

variable {n d : ℕ}

theorem chartDens_eq_posParts {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (hA : IsFiniteProjection J A) (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ)
    (y : Fin d → ℂ) :
    chartAbsDens J A f φ y = chartPosDens J A f φ y + chartPosDens J A (-f) φ y ∧
      chartDens J A f φ y = chartPosDens J A f φ y - chartPosDens J A (-f) φ y := by
  have hfin := IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y
  unfold chartAbsDens chartDens chartPosDens sheetSum
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine ⟨Finset.sum_congr rfl fun x _ => ?_, Finset.sum_congr rfl fun x _ => ?_⟩ <;>
    split_ifs <;> simp only [Pi.neg_apply, neg_mul, max_zero_add_max_neg_zero_eq_abs_self,
      max_zero_sub_max_neg_zero_eq_self, add_zero, sub_zero]

theorem chartPosDens_nonneg (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (hA : IsFiniteProjection J A) (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ)
    (y : Fin d → ℂ) : 0 ≤ chartPosDens J A f φ y := by
  unfold chartPosDens sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ (IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y)]
  exact Finset.sum_nonneg fun x _ => by split_ifs <;> simp

theorem measurable_chartPosDens {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (hA : IsFiniteProjection J A) {f : (Fin n → ℂ) → ℝ} (hf : Measurable f)
    (φ : Fin d → (Fin n → ℂ) → ℝ) : Measurable (chartPosDens J A f φ) :=
  SheetSumMeasurable.measurable_sheetSum hA (fun a b => max (a * b) 0)
    ((continuous_fst.mul continuous_snd).max continuous_const).measurable hf φ

theorem chartInt_eq_posParts {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (hA : IsFiniteProjection J A) {f : (Fin n → ℂ) → ℝ} (hf : Measurable f)
    (φ : Fin d → (Fin n → ℂ) → ℝ) :
    (Integrable (chartAbsDens J A f φ) ↔
      (∫⁻ y, ENNReal.ofReal (chartPosDens J A f φ y)) +
        ∫⁻ y, ENNReal.ofReal (chartPosDens J A (-f) φ y) < ⊤) ∧
    (Integrable (chartAbsDens J A f φ) → chartInt J A f φ =
      (∫⁻ y, ENNReal.ofReal (chartPosDens J A f φ y)).toReal -
        (∫⁻ y, ENNReal.ofReal (chartPosDens J A (-f) φ y)).toReal) := by
  have h0 := chartPosDens_nonneg J A hA f φ
  have h1 := chartPosDens_nonneg J A hA (-f) φ
  have m0 := measurable_chartPosDens hA hf φ
  have m1 := measurable_chartPosDens hA hf.neg φ
  have habs : chartAbsDens J A f φ = fun y => chartPosDens J A f φ y + chartPosDens J A (-f) φ y :=
    funext fun y => (chartDens_eq_posParts hA f φ y).1
  have hlin : ∫⁻ y, ENNReal.ofReal (chartAbsDens J A f φ y) =
      (∫⁻ y, ENNReal.ofReal (chartPosDens J A f φ y)) +
        ∫⁻ y, ENNReal.ofReal (chartPosDens J A (-f) φ y) := by
    rw [habs, ← lintegral_add_left m0.ennreal_ofReal]
    exact lintegral_congr fun y => ENNReal.ofReal_add (h0 y) (h1 y)
  have hint : Integrable (chartAbsDens J A f φ) ↔
      ∫⁻ y, ENNReal.ofReal (chartAbsDens J A f φ y) < ⊤ := by
    rw [habs, Integrable, hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun y => add_nonneg (h0 y) (h1 y))]
    exact and_iff_right (m0.add m1).aestronglyMeasurable
  refine ⟨hint.trans (by rw [hlin]), fun hi => ?_⟩
  have hi0 : Integrable (chartPosDens J A f φ) := hi.mono' m0.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (h0 y), habs]; linarith [h1 y])
  have hi1 : Integrable (chartPosDens J A (-f) φ) := hi.mono' m1.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (h1 y), habs]; linarith [h0 y])
  have hd : chartDens J A f φ = fun y => chartPosDens J A f φ y - chartPosDens J A (-f) φ y :=
    funext fun y => (chartDens_eq_posParts hA f φ y).2
  rw [chartInt, hd, integral_sub hi0 hi1,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall h0) m0.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall h1) m1.aestronglyMeasurable]

end IntegralIndep

theorem IntegralIndep.proof (h : PosPartIndep.Statement) : IntegralIndep.Statement := by
  intro n d J A A' f φ hP hd hA hA' hf hφ hi
  have e0 := h n d J A A' f φ hP hd hA hA' hf hφ
  have e1 := h n d J A A' (-f) φ hP hd hA hA' hf.neg hφ
  obtain ⟨iA, cA⟩ := IntegralIndep.chartInt_eq_posParts hA hf φ
  obtain ⟨iA', cA'⟩ := IntegralIndep.chartInt_eq_posParts hA' hf φ
  have hi' : Integrable (chartAbsDens J A' f φ) := iA'.2 (by rw [← e0, ← e1]; exact iA.1 hi)
  exact ⟨hi', by rw [cA hi, cA' hi', e0, e1]⟩

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchOffHypersurface
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

noncomputable section

def BranchOffHypersurface.Statement : Prop :=
  ∀ (n k : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (b : MvPolynomial (Fin n) ℂ) (U : Set (Fin k → ℂ))
    (φ : (Fin k → ℂ) → Fin n → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (k : ℕ) → b ∉ J →
    IsOpen U → U.Nonempty → DifferentiableOn ℂ φ U → Set.InjOn φ U → Set.MapsTo φ U (zeroSetIn J) →
    ∃ t ∈ U, eval (φ t) b ≠ 0

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.CMDepthAssoc
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing RingTheory.Sequence Pointwise

theorem length_le_ringKrullDim_quotient_colon {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (rs : List R) : ∀ {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] (y : M), y ≠ 0 →
      (∀ r ∈ rs, r ∈ maximalIdeal R) → IsWeaklyRegular M rs →
        (rs.length : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ Submodule.colon (⊥ : Submodule R M) {y}) := by
  induction rs with
  | nil =>
    intro M _ _ _ y hy _ _
    have hne : Submodule.colon (⊥ : Submodule R M) {y} ≠ ⊤ := by
      intro h
      have h1 : (1 : R) ∈ Submodule.colon (⊥ : Submodule R M) {y} := h ▸ Submodule.mem_top
      rw [Submodule.mem_colon_singleton, one_smul] at h1
      exact hy ((Submodule.mem_bot R).mp h1)
    have := Ideal.Quotient.nontrivial_iff.mpr hne
    simpa using (ringKrullDim_nonneg_of_nontrivial : 0 ≤ ringKrullDim (R ⧸ _))
  | cons x rs ih =>
    intro M _ _ _ y hy hmem hreg
    have hx : x ∈ maximalIdeal R := hmem x List.mem_cons_self
    have hmem' : ∀ r ∈ rs, r ∈ maximalIdeal R := fun r hr => hmem r (List.mem_cons_of_mem x hr)
    obtain ⟨hxreg, hrs⟩ := (isWeaklyRegular_cons_iff M x rs).mp hreg

    have hspan : Ideal.span {x} ≠ ⊤ := fun h =>
      (maximalIdeal.isMaximal R).ne_top (top_le_iff.mp (h ▸ (Ideal.span_le.mpr (by simpa using hx))))
    have hK := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := M) (Ideal.span {x}) hspan
    have hpow : ∀ k : ℕ, (Ideal.span {x} ^ k • ⊤ : Submodule R M) = x ^ k • ⊤ := fun k => by
      rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul]
    have hex : ∃ n : ℕ, y ∉ (Ideal.span {x} ^ n • ⊤ : Submodule R M) := by
      by_contra! h
      exact hy ((Submodule.mem_bot R).mp (hK ▸ Submodule.mem_iInf _ |>.mpr h))
    classical
    let n := Nat.find hex
    have hn : y ∉ (Ideal.span {x} ^ n • ⊤ : Submodule R M) := Nat.find_spec hex
    have hn0 : n ≠ 0 := by
      intro h0
      apply hn
      rw [h0, pow_zero, Ideal.one_eq_top, Submodule.top_smul]
      exact Submodule.mem_top
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    have hyk : y ∈ (Ideal.span {x} ^ k • ⊤ : Submodule R M) := by
      have := Nat.find_min hex (show k < n by omega)
      simpa using this
    rw [hpow] at hyk hn
    obtain ⟨y₁, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hyk
    have hy₁ : y₁ ∉ (x • ⊤ : Submodule R M) := by
      intro h
      obtain ⟨z, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h
      apply hn
      rw [hk, smul_smul, ← pow_succ]
      exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
    have hcolon : Submodule.colon (⊥ : Submodule R M) {x ^ k • y₁} =
        Submodule.colon (⊥ : Submodule R M) {y₁} := by
      ext r
      simp only [Submodule.mem_colon_singleton, Submodule.mem_bot]
      rw [smul_comm]
      constructor
      · intro h
        exact (hxreg.pow k) (show x ^ k • r • y₁ = x ^ k • 0 by rw [h, smul_zero])
      · intro h
        rw [h, smul_zero]
    rw [hcolon]

    set I := Submodule.colon (⊥ : Submodule R M) {y₁} with hI
    set ybar : QuotSMulTop x M := Submodule.Quotient.mk y₁ with hybar
    have hybar0 : ybar ≠ 0 := by
      rw [hybar, Ne, Submodule.Quotient.mk_eq_zero]
      exact hy₁
    have hih := ih ybar hybar0 hmem' hrs

    have hle : I ⊔ Ideal.span {x} ≤ Submodule.colon (⊥ : Submodule R (QuotSMulTop x M)) {ybar} := by
      refine sup_le ?_ ?_
      · intro r hr
        rw [hI, Submodule.mem_colon_singleton, Submodule.mem_bot] at hr
        rw [Submodule.mem_colon_singleton, Submodule.mem_bot, hybar, ← Submodule.Quotient.mk_smul, hr,
          Submodule.Quotient.mk_zero]
      · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Submodule.mem_colon_singleton,
          Submodule.mem_bot, hybar, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
        exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
    have hd1 : ringKrullDim (R ⧸ Submodule.colon (⊥ : Submodule R (QuotSMulTop x M)) {ybar}) ≤
        ringKrullDim (R ⧸ (I ⊔ Ideal.span {x})) :=
      ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hle)

    have hnzd : Ideal.Quotient.mk I x ∈ nonZeroDivisors (R ⧸ I) := by
      rw [mem_nonZeroDivisors_iff_right]
      intro z hz
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, hI, Submodule.mem_colon_singleton,
        Submodule.mem_bot, mul_smul, smul_comm] at hz
      rw [Ideal.Quotient.eq_zero_iff_mem, hI, Submodule.mem_colon_singleton, Submodule.mem_bot]
      exact hxreg (show x • r • y₁ = x • 0 by rw [hz, smul_zero])
    have hd2 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hnzd
    have heq : (R ⧸ I) ⧸ Ideal.span {Ideal.Quotient.mk I x} ≃+* R ⧸ (I ⊔ Ideal.span {x}) := by
      have : Ideal.span {Ideal.Quotient.mk I x} = (Ideal.span {x}).map (Ideal.Quotient.mk I) := by
        rw [Ideal.map_span, Set.image_singleton]
      rw [this]
      exact DoubleQuot.quotQuotEquivQuotSup I (Ideal.span {x})
    rw [ringKrullDim_eq_of_ringEquiv heq] at hd2
    calc ((x :: rs).length : WithBot ℕ∞) = (rs.length : WithBot ℕ∞) + 1 := by simp
      _ ≤ ringKrullDim (R ⧸ Submodule.colon (⊥ : Submodule R (QuotSMulTop x M)) {ybar}) + 1 := by
          gcongr
      _ ≤ ringKrullDim (R ⧸ (I ⊔ Ideal.span {x})) + 1 := by gcongr
      _ ≤ ringKrullDim (R ⧸ I) := hd2

theorem ringKrullDim_quotient_eq_of_mem_minimalPrimes {B : Type*} [CommRing B] [IsCohenMacaulayLocalRing B]
    {P : Ideal B} (hP : P ∈ minimalPrimes B) : ringKrullDim (B ⧸ P) = ringKrullDim B := by
  obtain ⟨rs, hm, hreg, hdim⟩ := IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := B)
  have hann : Module.annihilator B B = ⊥ := Module.annihilator_eq_bot.mpr inferInstance
  have hP' : P ∈ (Module.annihilator B B).minimalPrimes := by
    rw [hann]
    exact hP
  have hA := Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes B B hP'
  obtain ⟨hprime, y, hy⟩ := (isAssociatedPrime_iff.mp hA)
  have hy0 : y ≠ 0 := by
    rintro rfl
    apply hprime.ne_top
    rw [hy, eq_top_iff]
    intro r _
    rw [Submodule.mem_colon_singleton, smul_zero]
    exact Submodule.zero_mem _
  have hD := length_le_ringKrullDim_quotient_colon rs y hy0 hm hreg
  rw [← hy, ← hdim] at hD
  exact le_antisymm (ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective) hD

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPosPartLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

namespace PosPartLocal

variable {n d : ℕ}

theorem chartPosDens_eq {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {s : (Fin d → ℂ) → Fin n → ℂ} {U : Set (Fin d → ℂ)} {W E : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hsd : DifferentiableOn ℂ s U)
    (hsec : ∀ y ∈ U, A *ᵥ s y = y ∧ s y ∈ zeroSet J)
    (hW : IsOpen W) (hWs : ∀ x' ∈ zeroSet J ∩ W, A *ᵥ x' ∈ U ∧ s (A *ᵥ x') = x')
    (hEW : E ⊆ W) (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ) :
    chartPosDens J A (E.indicator f) φ y = (U ∩ s ⁻¹' E).indicator
      (fun y => max (f (s y) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y) 0) y := by
  classical
  unfold chartPosDens sheetSum
  by_cases hy : y ∈ U ∩ s ⁻¹' E
  · rw [Set.indicator_of_mem hy]
    have hfib : s y ∈ ComplexSets.fibre J A y := ⟨(hsec y hy.1).2, (hsec y hy.1).1⟩
    have hsh : IsSheetAt J A (s y) s :=
      ⟨U, hU, by rw [(hsec y hy.1).1]; exact hy.1, hsd, by rw [(hsec y hy.1).1], hsec, W,
        hW.mem_nhds (hEW hy.2), fun x' hx' _ => (hWs x' hx').2.symm⟩
    rw [finsum_eq_single _ (s y) ?_, finsum_eq_if, if_pos hfib, dite_eq_left ⟨s, hsh⟩]
    · have h := SheetSumMeasurable.term_eq (fun a b => max (a * b) 0) (E.indicator f) φ hsh ⟨s, hsh⟩
      rw [(hsec y hy.1).1] at h
      dsimp only
      rw [h, Set.indicator_of_mem (show s y ∈ E from hy.2)]
    · intro x hne
      rw [finsum_eq_if]
      split_ifs with hx h
      · have hxE : x ∉ E := fun hxE => hne (by
          have h' := (hWs x ⟨hx.1, hEW hxE⟩).2
          rw [hx.2] at h'
          exact h'.symm)
        dsimp only
        rw [Set.indicator_of_notMem hxE, zero_mul, max_self]
      · rfl
      · rfl
  · rw [Set.indicator_of_notMem hy]
    refine finsum_mem_eq_zero_of_forall_eq_zero fun x hx => ?_
    split_ifs with h
    · have hxE : x ∉ E := fun hxE => hy (by
        obtain ⟨h1, h2⟩ := hWs x ⟨hx.1, hEW hxE⟩
        rw [hx.2] at h1 h2
        exact ⟨h1, by rw [Set.mem_preimage, h2]; exact hxE⟩)
      dsimp only
      rw [Set.indicator_of_notMem hxE, zero_mul, max_self]
    · rfl

end PosPartLocal

theorem PosPartLocal.proof : PosPartLocal.Statement := by
  rintro n d J A A' f φ x - hφ ⟨s, U, hU, hxU, hsd, -, hsec, V, hV, hVs⟩
    ⟨s', U', hU', hxU', hsd', -, hsec', V', hV', hVs'⟩
  have hAc : Continuous fun z : Fin n → ℂ => A *ᵥ z := by fun_prop
  have hAc' : Continuous fun z : Fin n → ℂ => A' *ᵥ z := by fun_prop
  set W := (interior V ∩ (fun z => A *ᵥ z) ⁻¹' U) ∩ (interior V' ∩ (fun z => A' *ᵥ z) ⁻¹' U')
    with hWdef
  have hW : IsOpen W :=
    (isOpen_interior.inter (hU.preimage hAc)).inter (isOpen_interior.inter (hU'.preimage hAc'))
  have hWs : ∀ x' ∈ zeroSet J ∩ W, A *ᵥ x' ∈ U ∧ s (A *ᵥ x') = x' :=
    by rintro x' ⟨hZ, ⟨hV1, hU1⟩, -⟩; exact ⟨hU1, (hVs x' ⟨hZ, interior_subset hV1⟩ hU1).symm⟩
  have hWs' : ∀ x' ∈ zeroSet J ∩ W, A' *ᵥ x' ∈ U' ∧ s' (A' *ᵥ x') = x' :=
    by rintro x' ⟨hZ, -, ⟨hV1, hU1⟩⟩; exact ⟨hU1, (hVs' x' ⟨hZ, interior_subset hV1⟩ hU1).symm⟩
  refine ⟨W, hW, ⟨⟨mem_interior_iff_mem_nhds.2 hV, hxU⟩, ⟨mem_interior_iff_mem_nhds.2 hV', hxU'⟩⟩,
    fun E _ hEW => ?_⟩
  simp_rw [PosPartLocal.chartPosDens_eq hU hsd hsec hW hWs hEW,
    PosPartLocal.chartPosDens_eq hU' hsd' hsec' hW hWs' hEW]

  set O' := U' ∩ s' ⁻¹' W with hO'def
  set τ : (Fin d → ℂ) → Fin d → ℂ := fun z => A *ᵥ s' z with hτdef
  have hO' : IsOpen O' := hsd'.continuousOn.isOpen_inter_preimage hU' hW
  have hτU : ∀ z ∈ O', τ z ∈ U ∧ s (τ z) = s' z := fun z hz => hWs _ ⟨(hsec' z hz.1).2, hz.2⟩
  have hτd : DifferentiableOn ℂ τ O' := by
    have hs'O : DifferentiableOn ℂ s' O' := hsd'.mono Set.inter_subset_left
    exact ((Matrix.mulVecLin A).toContinuousLinearMap.differentiable.comp_differentiableOn hs'O)
  have hτan : AnalyticOnNhd ℂ τ O' := IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_differentiableOn hO' hτd
  have hτinj : Set.InjOn τ O' := fun z₁ h₁ z₂ h₂ h => by
    have h' := congrArg s h
    rw [(hτU z₁ h₁).2, (hτU z₂ h₂).2] at h'
    rw [← (hsec' z₁ h₁.1).1, ← (hsec' z₂ h₂.1).1, h']
  have hsan : AnalyticOnNhd ℂ s U := IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_differentiableOn hU hsd
  calc _ = ∫⁻ y in τ '' O', ENNReal.ofReal ((U ∩ s ⁻¹' E).indicator
          (fun y => max (f (s y) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y) 0) y) := by
        refine (setLIntegral_eq_of_support_subset fun y hy => ?_).symm
        have hyE : y ∈ U ∩ s ⁻¹' E := by
          by_contra h
          exact hy (by simp [Set.indicator_of_notMem h])
        have hZ : s y ∈ zeroSet J ∩ W := ⟨(hsec y hyE.1).2, hEW hyE.2⟩
        refine ⟨A' *ᵥ s y, ⟨(hWs' _ hZ).1, ?_⟩, ?_⟩
        · show s' (A' *ᵥ s y) ∈ W
          rw [(hWs' _ hZ).2]
          exact hZ.2
        · show A *ᵥ s' (A' *ᵥ s y) = y
          rw [(hWs' _ hZ).2, (hsec y hyE.1).1]
    _ = ∫⁻ z in O', ENNReal.ofReal (Complex.normSq (ReciprocityTheory.AnForm.A.jacC τ z).det) *
          ENNReal.ofReal ((U ∩ s ⁻¹' E).indicator
            (fun y => max (f (s y) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y) 0) (τ z)) :=
        ReciprocityTheory.AnForm.A.lintegral_image_eq_lintegral_normSq_det_mul τ O' hO' hτan hτinj _
    _ = ∫⁻ z in O', ENNReal.ofReal ((U' ∩ s' ⁻¹' E).indicator
          (fun y => max (f (s' y) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s') y) 0) z) := by
        refine setLIntegral_congr_fun hO'.measurableSet fun z hz => ?_
        by_cases hzE : s' z ∈ E
        · have hm : τ z ∈ U ∩ s ⁻¹' E :=
            ⟨(hτU z hz).1, by rw [Set.mem_preimage, (hτU z hz).2]; exact hzE⟩
          rw [Set.indicator_of_mem hm, Set.indicator_of_mem (show z ∈ U' ∩ s' ⁻¹' E from ⟨hz.1, hzE⟩)]
          have h1 : ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s') z =
              ReciprocityTheory.AnForm.maDens (fun k => (φ k ∘ s) ∘ τ) z :=
            IndefiniteRowSideFullHecke.ComplexSets.maDens_congr_of_eventuallyEq fun k => by
              filter_upwards [hO'.mem_nhds hz] with w hw
              show φ k (s' w) = φ k (s (τ w))
              rw [(hτU w hw).2]
          have h2 : ReciprocityTheory.AnForm.maDens (fun k => (φ k ∘ s) ∘ τ) z =
              ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) (τ z) *
                Complex.normSq (ReciprocityTheory.AnForm.A.jacC τ z).det := by
            refine ReciprocityTheory.AnForm.A.maDens_comp (fun k => φ k ∘ s) τ z (hτan z hz) fun k => ?_
            obtain ⟨Ok, hOk, hZOk, hφk⟩ := hφ k
            have hsZ : s (τ z) ∈ Ok := hZOk (by rw [(hτU z hz).2]; exact (hsec' z hz.1).2)
            have hφa : ContDiffAt ℝ 2 (φ k) (s (τ z)) :=
              (hφk.contDiffAt (hOk.mem_nhds hsZ)).of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
            have hsa : ContDiffAt ℝ 2 s (τ z) :=
              ((hsan (τ z) (hτU z hz).1).contDiffAt).restrict_scalars ℝ
            exact hφa.comp (τ z) hsa
          rw [h1, h2, (hτU z hz).2, ← ENNReal.ofReal_mul (Complex.normSq_nonneg _), mul_comm,
            max_mul_of_nonneg _ _ (Complex.normSq_nonneg _), zero_mul, mul_assoc]
        · rw [Set.indicator_of_notMem (fun hm => hzE (by
              have := hm.2
              rw [Set.mem_preimage, (hτU z hz).2] at this
              exact this)),
            Set.indicator_of_notMem (show z ∉ U' ∩ s' ⁻¹' E from fun hm => hzE hm.2)]
          simp
    _ = _ := by
        refine setLIntegral_eq_of_support_subset fun z hz => ?_
        have hzE : z ∈ U' ∩ s' ⁻¹' E := by
          by_contra h
          exact hz (by simp [Set.indicator_of_notMem h])
        exact ⟨hzE.1, hEW hzE.2⟩

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLocalDimDomain
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

def LocalDimDomain.Statement : Prop :=
  ∀ (n e : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (e : ℕ) → ∀ q ∈ zeroSet J,
      ringKrullDim (localRingAt J q) = (e : ℕ)

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceCMUnmixed
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets IsLocalRing

def SliceCMUnmixed.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (L : Matrix (Fin d) (Fin n) ℂ) (q : Fin n → ℂ),
    IsCohenMacaulayAt J q → ringKrullDim (localRingAt J q) = (d + 1 : ℕ) →
    ringKrullDim (localRingAt (sliceIdeal J L q) q) = (1 : ℕ) →
      ∀ P ∈ associatedPrimes (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ ⧸ sliceIdeal J L q),
        P ≤ RingHom.ker (eval q) →
          P ∈ (sliceIdeal J L q).minimalPrimes ∧ P ≠ RingHom.ker (eval q)

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchInComponent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

def BranchInComponent.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (k : ℕ) (q : Fin n → ℂ) (c : VarBranch I k q),
    ∃ J ∈ I.minimalPrimes, Set.MapsTo c.toFun (Metric.ball 0 c.radius) (zeroSet J)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveRegularOffCentre
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def CurveRegularOffCentre.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ),
    ringKrullDim (curveLocalRing I q) = 1 →
      ∃ N ∈ 𝓝 q, ∀ x ∈ zeroSet I ∩ N, x ≠ q →
        ∃ (A : (Fin n → ℂ) →L[ℂ] ℂ) (O : Set ℂ) (V : Set (Fin n → ℂ)) (g : ℂ → Fin n → ℂ),
          IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ y ∈ O, A (g y) = y) ∧
            zeroSet I ∩ V = g '' O

end

end GroundTheory.Heights₂.Heights
end
