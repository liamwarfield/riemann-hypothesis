module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.AffineOfCone
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegFixedBallMass
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeTangentAverage

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetAreaCompare
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

open scoped ENNReal

noncomputable section

namespace SheetAreaCompare

variable {n d : ℕ}

theorem measurable_sheetJac (s : (Fin d → ℂ) → Fin n → ℂ) : Measurable (sheetJac s) := by
  let φ : EuclideanSpace ℂ (Fin d) →L[ℝ] (Fin d → ℂ) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℂ)).toContinuousLinearMap
  let ψ : (Fin n → ℂ) →L[ℝ] EuclideanSpace ℂ (Fin n) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℂ)).symm.toContinuousLinearMap
  have h : sheetJac s = (fun M : EuclideanSpace ℂ (Fin d) →L[ℝ] EuclideanSpace ℂ (Fin n) =>
      areaJacobian (M : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ (Fin n))) ∘
        (fun L : (Fin d → ℂ) →L[ℝ] (Fin n → ℂ) => ψ.comp (L.comp φ)) ∘ fderiv ℝ s := by
    funext y
    rfl
  rw [h]
  have hc : Continuous fun L : (Fin d → ℂ) →L[ℝ] (Fin n → ℂ) => ψ.comp (L.comp φ) := by fun_prop
  exact continuous_areaJacobian.measurable.comp (hc.measurable.comp (measurable_fderiv ℝ s))

theorem exists_lintegral_volume_eq (d : ℕ) : ∃ c : NNReal, ∀ F : (Fin d → ℂ) → ℝ≥0∞,
    ∫⁻ y, F y = c * ∫⁻ y, F (WithLp.ofLp y)
      ∂(μH[((2 * d : ℕ) : ℝ)] : Measure (EuclideanSpace ℂ (Fin d))) := by
  let e := (EuclideanSpace.equiv (Fin d) ℂ).toHomeomorph.toMeasurableEquiv
  let ν : Measure (Fin d → ℂ) := (μH[((2 * d : ℕ) : ℝ)] : Measure (EuclideanSpace ℂ (Fin d))).map e
  have : ν.IsAddHaarMeasure := (EuclideanSpace.equiv (Fin d) ℂ).isAddHaarMeasure_map _
  refine ⟨Measure.addHaarScalarFactor volume ν, fun F => ?_⟩
  conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul volume ν]
  rw [lintegral_smul_measure, lintegral_map_equiv F e]
  rfl

theorem ofReal_finsum_le_tsum {α : Type*} (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    ENNReal.ofReal (∑ᶠ a, f a) ≤ ∑' a, ENNReal.ofReal (f a) := by
  by_cases h : (Function.support f).Finite
  · rw [finsum_eq_sum f h, ENNReal.ofReal_sum_of_nonneg fun a _ => hf a]
    exact ENNReal.sum_le_tsum _
  · rw [finsum_of_infinite_support h]
    simp

theorem exists_sheet_nhds {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (x : Fin n → ℂ) :
    ∃ (s : (Fin d → ℂ) → Fin n → ℂ) (U : Set (Fin d → ℂ)) (W : Set (Fin n → ℂ)),
      IsOpen U ∧ IsOpen W ∧ DifferentiableOn ℂ s U ∧ (∀ y ∈ U, A *ᵥ s y = y ∧ s y ∈ zeroSet J) ∧
      (∀ x' ∈ zeroSet J ∩ W, A *ᵥ x' ∈ U ∧ IsSheetAt J A x' s) ∧
      ((∃ s, IsSheetAt J A x s) → x ∈ W) := by
  by_cases hx : ∃ s, IsSheetAt J A x s
  · obtain ⟨s, U, hU, hxU, hsd, hsx, hsec, V, hV, hVs⟩ := hx
    have hAc : Continuous fun z : Fin n → ℂ => A *ᵥ z := by fun_prop
    refine ⟨s, U, interior V ∩ (fun z => A *ᵥ z) ⁻¹' U, hU,
      isOpen_interior.inter (hU.preimage hAc), hsd, hsec, ?_, fun _ =>
        ⟨mem_interior_iff_mem_nhds.2 hV, hxU⟩⟩
    rintro x' ⟨hx'Z, hx'V, hx'U⟩
    have hx's : s (A *ᵥ x') = x' := (hVs x' ⟨hx'Z, interior_subset hx'V⟩ hx'U).symm
    exact ⟨hx'U, U, hU, hx'U, hsd, hx's, hsec, interior V, isOpen_interior.mem_nhds hx'V,
      fun x'' hx'' hAx'' => hVs x'' ⟨hx''.1, interior_subset hx''.2⟩ hAx''⟩
  · exact ⟨fun _ => x, ∅, ∅, isOpen_empty, isOpen_empty, differentiableOn_empty, by simp,
      by simp, fun h => absurd h hx⟩

end SheetAreaCompare


open SheetAreaCompare in
theorem SheetAreaCompare.proof (h₁ : SheetImageArea.Statement) : SheetAreaCompare.Statement := by
  classical
  intro n d J A
  obtain ⟨c, hc⟩ := exists_lintegral_volume_eq d
  refine ⟨c, ENNReal.coe_lt_top, fun h hh => ?_⟩
  choose σ U W hU hW hσd hσsec hWsh hxW using
    fun x : Fin n → ℂ => exists_sheet_nhds (J := J) (A := A) x

  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hW
  obtain ⟨e, he⟩ := (hTc.insert 0).exists_eq_range (Set.insert_nonempty 0 T)
  have hcover : ∀ x, (∃ s, IsSheetAt J A x s) → ∃ k, x ∈ W (e k) := by
    intro x hx
    have : x ∈ ⋃ i ∈ T, W i := hTU ▸ Set.mem_iUnion.2 ⟨x, hxW x hx⟩
    obtain ⟨i, hiT, hxi⟩ := Set.mem_iUnion₂.1 this
    obtain ⟨k, rfl⟩ : i ∈ Set.range e := he ▸ Set.mem_insert_of_mem 0 hiT
    exact ⟨k, hxi⟩

  set E : ℕ → Set (Fin n → ℂ) := fun k => zeroSet J ∩ disjointed (fun k => W (e k)) k with hE
  have hEm : ∀ k, MeasurableSet (E k) := fun k =>
    (SheetSumMeasurable.isClosed_zeroSet J).measurableSet.inter
      (MeasurableSet.disjointed (fun k => (hW (e k)).measurableSet) k)
  have hEW : ∀ k, E k ⊆ zeroSet J ∩ W (e k) := fun k x hx =>
    ⟨hx.1, disjointed_subset (fun k => W (e k)) k hx.2⟩
  have hEdisj : Pairwise fun k k' => Disjoint (E k) (E k') := fun k k' hkk' =>
    (disjoint_disjointed (fun k => W (e k)) hkk').mono Set.inter_subset_right Set.inter_subset_right
  have hEcover : ∀ x, (∃ s, IsSheetAt J A x s) → ∃ k, x ∈ E k := by
    intro x hx
    obtain ⟨m, hm⟩ := hcover x hx
    have hxZ : x ∈ zeroSet J := by
      obtain ⟨s, U₀, -, hxU₀, -, hsx, hsec, -⟩ := hx
      rw [← hsx]
      exact (hsec _ hxU₀).2
    have : x ∈ ⋃ k, disjointed (fun k => W (e k)) k := by
      rw [iUnion_disjointed]
      exact Set.mem_iUnion.2 ⟨m, hm⟩
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 this
    exact ⟨k, hxZ, hk⟩

  set σ' : ℕ → (Fin d → ℂ) → Fin n → ℂ := fun k => (U (e k)).piecewise (σ (e k)) fun _ => 0
    with hσ'
  have hσ'm : ∀ k, Measurable (σ' k) := fun k =>
    (hσd (e k)).continuousOn.measurable_piecewise continuousOn_const (hU (e k)).measurableSet
  have hσ'eq : ∀ k, ∀ y ∈ U (e k), σ' k y = σ (e k) y := fun k y hy => by
    simp [hσ', Set.piecewise_eq_of_mem _ _ _ hy]
  set B : ℕ → Set (Fin d → ℂ) := fun k => U (e k) ∩ σ' k ⁻¹' E k with hB
  have hBm : ∀ k, MeasurableSet (B k) := fun k =>
    (hU (e k)).measurableSet.inter (hσ'm k (hEm k))
  have hBmem : ∀ k y, y ∈ B k ↔ y ∈ U (e k) ∧ σ (e k) y ∈ E k := by
    intro k y
    constructor
    · rintro ⟨hy, hy'⟩
      exact ⟨hy, by simpa [Set.mem_preimage, hσ'eq k y hy] using hy'⟩
    · rintro ⟨hy, hy'⟩
      exact ⟨hy, by simpa [Set.mem_preimage, hσ'eq k y hy] using hy'⟩
  set G : ℕ → (Fin d → ℂ) → ℝ≥0∞ := fun k y =>
    ‖h (σ' k y)‖ₑ * ENNReal.ofReal (sheetJac (σ (e k)) y) with hG
  have hGm : ∀ k, Measurable (G k) := fun k =>
    (hh.comp (hσ'm k)).enorm.mul (ENNReal.measurable_ofReal.comp (measurable_sheetJac _))

  set t : (Fin n → ℂ) → ℝ := fun x => if hx : ∃ s, IsSheetAt J A x s then
    |h x| * sheetJac hx.choose (A *ᵥ x) else 0 with ht
  have ht0 : ∀ x, 0 ≤ t x := by
    intro x
    simp only [ht]
    split_ifs
    · exact mul_nonneg (abs_nonneg _) (sheetJac_nonneg _ _)
    · exact le_rfl
  have htE : ∀ k x, x ∈ E k →
      ENNReal.ofReal (t x) = G k (A *ᵥ x) ∧ A *ᵥ x ∈ B k ∧ σ (e k) (A *ᵥ x) = x := by
    intro k x hx
    obtain ⟨hAU, hsh⟩ := hWsh (e k) x (hEW k hx)
    have hsx : σ (e k) (A *ᵥ x) = x := by
      obtain ⟨-, -, -, -, hsx, -⟩ := hsh
      exact hsx
    have hex : ∃ s, IsSheetAt J A x s := ⟨_, hsh⟩
    have hJ : sheetJac hex.choose (A *ᵥ x) = sheetJac (σ (e k)) (A *ᵥ x) := by
      unfold sheetJac
      rw [(SheetSumMeasurable.sheet_eventuallyEq hsh hex.choose_spec).fderiv_eq]
    refine ⟨?_, (hBmem k _).2 ⟨hAU, hsx.symm ▸ hx⟩, hsx⟩
    simp only [ht, dif_pos hex, hG, hσ'eq k _ hAU, hsx, hJ]
    rw [ENNReal.ofReal_mul (abs_nonneg _), Real.enorm_eq_ofReal_abs]

  have hpt : ∀ y, ‖sheetSum J A (fun x s => |h x| * sheetJac s (A *ᵥ x)) y‖ₑ ≤
      ∑' k, (B k).indicator (G k) y := by
    intro y
    have hS : sheetSum J A (fun x s => |h x| * sheetJac s (A *ᵥ x)) y =
        ∑ᶠ x, (ComplexSets.fibre J A y).indicator t x := by
      unfold sheetSum
      rw [finsum_mem_def]
    have hnn : ∀ x, 0 ≤ (ComplexSets.fibre J A y).indicator t x := fun x =>
      Set.indicator_nonneg (fun x _ => ht0 x) x
    rw [hS, Real.enorm_eq_ofReal (finsum_nonneg hnn)]
    calc ENNReal.ofReal (∑ᶠ x, (ComplexSets.fibre J A y).indicator t x)
        ≤ ∑' x, ENNReal.ofReal ((ComplexSets.fibre J A y).indicator t x) := ofReal_finsum_le_tsum _ hnn
      _ ≤ ∑' x, ∑' k, (E k ∩ ComplexSets.fibre J A y).indicator (fun x => ENNReal.ofReal (t x)) x := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        by_cases hxf : x ∈ ComplexSets.fibre J A y
        · by_cases hx : ∃ s, IsSheetAt J A x s
          · obtain ⟨k, hk⟩ := hEcover x hx
            rw [Set.indicator_of_mem hxf]
            have hle : (E k ∩ ComplexSets.fibre J A y).indicator (fun x => ENNReal.ofReal (t x)) x ≤
                ∑' k, (E k ∩ ComplexSets.fibre J A y).indicator (fun x => ENNReal.ofReal (t x)) x :=
              le_tsum (fun k => (E k ∩ ComplexSets.fibre J A y).indicator (fun x => ENNReal.ofReal (t x)) x) k
            exact (Set.indicator_of_mem (show x ∈ E k ∩ ComplexSets.fibre J A y from ⟨hk, hxf⟩)
              (fun x => ENNReal.ofReal (t x))).symm.le.trans hle
          · have : t x = 0 := by simp only [ht, dif_neg hx]
            rw [Set.indicator_of_mem hxf, this, ENNReal.ofReal_zero]
            exact zero_le
        · rw [Set.indicator_of_notMem hxf, ENNReal.ofReal_zero]
          exact zero_le
      _ = ∑' k, ∑' x, (E k ∩ ComplexSets.fibre J A y).indicator (fun x => ENNReal.ofReal (t x)) x :=
        ENNReal.tsum_comm
      _ ≤ ∑' k, (B k).indicator (G k) y := by
        refine ENNReal.tsum_le_tsum fun k => ?_
        rw [tsum_eq_single (σ (e k) y)]
        · by_cases hm : σ (e k) y ∈ E k ∩ ComplexSets.fibre J A y
          · rw [Set.indicator_of_mem hm]
            obtain ⟨h1, h2, -⟩ := htE k _ hm.1
            have hAy : A *ᵥ σ (e k) y = y := hm.2.2
            rw [hAy] at h1 h2
            rw [h1, Set.indicator_of_mem h2]
          · rw [Set.indicator_of_notMem hm]
            exact zero_le
        · intro x hne
          refine Set.indicator_of_notMem (fun hx => hne ?_) _
          obtain ⟨-, -, hsx⟩ := htE k x hx.1
          have hAx : A *ᵥ x = y := hx.2.2
          rw [← hAx, hsx]

  have hpiece : ∀ k, ∫⁻ y, (B k).indicator (G k) y = c * ∫⁻ z in (WithLp.ofLp ⁻¹' E k : Set (EuclideanSpace ℂ (Fin n))),
      ‖h (WithLp.ofLp z)‖ₑ ∂(μH[((2 * d : ℕ) : ℝ)]) := by
    intro k
    have hBm' : MeasurableSet (WithLp.ofLp ⁻¹' B k : Set (EuclideanSpace ℂ (Fin d))) :=
      (EuclideanSpace.equiv (Fin d) ℂ).continuous.measurable (hBm k)
    rw [hc]
    congr 1
    have h2 := h₁ n d A (U (e k)) (σ (e k)) (hU (e k)) (hσd (e k)) (fun y hy => (hσsec (e k) y hy).1)
      (WithLp.ofLp ⁻¹' B k) hBm' (fun y hy => hy.1) (fun z => ‖h (WithLp.ofLp z)‖ₑ)
      (hh.comp (EuclideanSpace.equiv (Fin n) ℂ).continuous.measurable).enorm
    have himg : (fun y : EuclideanSpace ℂ (Fin d) => WithLp.toLp 2 (σ (e k) (WithLp.ofLp y))) ''
        (WithLp.ofLp ⁻¹' B k) = WithLp.ofLp ⁻¹' E k := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ((hBmem k _).1 hy).2
      · intro hz
        obtain ⟨-, h2, h3⟩ := htE k _ hz
        exact ⟨WithLp.toLp 2 (A *ᵥ WithLp.ofLp z), h2, by simp [h3]⟩
    rw [himg] at h2
    rw [← h2, ← lintegral_indicator hBm']
    refine lintegral_congr fun y => ?_
    by_cases hy : y ∈ WithLp.ofLp ⁻¹' B k
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (show WithLp.ofLp y ∈ B k from hy)]
      simp [hG, hσ'eq k _ hy.1]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem (show WithLp.ofLp y ∉ B k from hy)]
  have hImeas : ∀ k, MeasurableSet (WithLp.ofLp ⁻¹' E k : Set (EuclideanSpace ℂ (Fin n))) :=
    fun k => (EuclideanSpace.equiv (Fin n) ℂ).continuous.measurable (hEm k)
  have hIdisj : Pairwise fun k k' => Disjoint (WithLp.ofLp ⁻¹' E k : Set (EuclideanSpace ℂ (Fin n)))
      (WithLp.ofLp ⁻¹' E k') :=
    fun k k' hkk' => (hEdisj hkk').preimage _
  have hIsub : (⋃ k, (WithLp.ofLp ⁻¹' E k : Set (EuclideanSpace ℂ (Fin n)))) ⊆ zeroSetEuc J := by
    intro z hz
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hz
    intro q hq
    exact (hEW k hk).1 q hq
  calc ∫⁻ y, ‖sheetSum J A (fun x s => |h x| * sheetJac s (A *ᵥ x)) y‖ₑ
      ≤ ∫⁻ y, ∑' k, (B k).indicator (G k) y := lintegral_mono hpt
    _ = ∑' k, ∫⁻ y, (B k).indicator (G k) y :=
        lintegral_tsum fun k => ((hGm k).indicator (hBm k)).aemeasurable
    _ = c * ∫⁻ z in ⋃ k, (WithLp.ofLp ⁻¹' E k : Set (EuclideanSpace ℂ (Fin n))), ‖h (WithLp.ofLp z)‖ₑ ∂(μH[((2 * d : ℕ) : ℝ)]) := by
        rw [lintegral_iUnion hImeas hIdisj, ← ENNReal.tsum_mul_left]
        exact tsum_congr hpiece
    _ ≤ c * ∫⁻ z in zeroSetEuc J, ‖h (WithLp.ofLp z)‖ₑ ∂(μH[((2 * d : ℕ) : ℝ)]) :=
        mul_le_mul_of_nonneg_left (lintegral_mono_set hIsub) zero_le

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPuncturedCurveDiscInverse
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def PuncturedCurveDiscInverse.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ),
    IsRadicalAt I q → ringKrullDim (curveLocalRing I q) = 1 →
    ∃ ε > 0, ∀ (φ : ℂ → Fin n → ℂ) (σ₀ : ℂ) (δ : ℝ), 0 < δ →
      DifferentiableOn ℂ φ (Metric.ball σ₀ δ) → Set.InjOn φ (Metric.ball σ₀ δ) →
      Set.MapsTo φ (Metric.ball σ₀ δ) (zeroSet I) → φ σ₀ ∈ Metric.ball q ε → φ σ₀ ≠ q →
      ∃ U : Set (Fin n → ℂ), IsOpen U ∧ φ σ₀ ∈ U ∧ ∃ ψ : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ ψ U ∧
        ∀ z ∈ zeroSet I ∩ U, ∃ σ ∈ Metric.ball σ₀ δ, φ σ = z ∧ ψ z = σ

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimeBranchPlace
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

def PrimeBranchPlace.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (c : VarBranch J 1 q),
    J.IsPrime → ringKrullDim (curveLocalRing J q) ≤ 1 →
      ∃ P : MaximalSpectrum (curveNormalisation J q), ∀ f : MvPolynomial (Fin n) ℂ,
        Ring.ord (Localization.AtPrime P.asIdeal)
            (algebraMap (curveNormalisation J q) (Localization.AtPrime P.asIdeal)
              (algebraMap (curveLocalRing J q) (curveNormalisation J q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing J q) f))) = branchOrder c f

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalisationModelLocalization
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

def normalModelSubmonoid {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    (q : Fin n → ℂ) : Submonoid (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) :=
  (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)).primeCompl.map
    ((Ideal.Quotient.mk M.ideal).comp
      (rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin M.m) ℂ).toRingHom)

theorem mk_rename_mem_normalModelSubmonoid {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J) (q : Fin n → ℂ) (f : MvPolynomial (Fin n) ℂ) (hf : eval q f ≠ 0) :
    Ideal.Quotient.mk M.ideal (rename Sum.inl f) ∈ normalModelSubmonoid M q :=
  Submonoid.mem_map_of_mem _ (show f ∈ (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)).primeCompl from
    fun h ↦ hf (RingHom.mem_ker.1 h))

theorem zero_not_mem_normalModelSubmonoid {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J) (q : Fin n → ℂ) (hq : q ∈ zeroSet J) :
    (0 : MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) ∉ normalModelSubmonoid M q := by
  rintro ⟨f, hf, h0⟩
  apply hf
  refine RingHom.mem_ker.2 (hq f ?_)
  rw [← M.comap_eq, Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
  exact h0

def NormalisationModelLocalization.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J),
    J.IsPrime →
      ∃ e : curveNormalisation J q ≃+* Localization (normalModelSubmonoid M q),
        ∀ f : MvPolynomial (Fin n) ℂ,
          e (algebraMap (curveLocalRing J q) (curveNormalisation J q)
              (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing J q) f)) =
            algebraMap (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) (Localization (normalModelSubmonoid M q))
              (Ideal.Quotient.mk M.ideal (rename Sum.inl f))

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegRadialWeight
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def radialTransform (d : ℕ) (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  a t * t ^ d - ∫ τ in (0 : ℝ)..t, a τ * ((d : ℝ) * τ ^ (d - 1))

theorem radialTransform_zero (a : ℝ → ℝ) : radialTransform 0 a = a := by
  funext t
  simp [radialTransform]

theorem integral_const_mul_dpow (e : ℕ) (c t : ℝ) :
    ∫ τ in (0 : ℝ)..t, c * (((e + 1 : ℕ) : ℝ) * τ ^ (e + 1 - 1)) = c * t ^ (e + 1) := by
  simp only [Nat.add_sub_cancel]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_pow]
  push_cast
  field_simp
  ring

theorem radialTransform_eq_zero_of_const (e : ℕ) (a : ℝ → ℝ) {t₀ t : ℝ}
    (ha : ∀ τ ∈ Set.Icc 0 t₀, a τ = a 0) (ht : t ∈ Set.Icc 0 t₀) :
    radialTransform (e + 1) a t = 0 := by
  have hint : ∫ τ in (0 : ℝ)..t, a τ * (((e + 1 : ℕ) : ℝ) * τ ^ (e + 1 - 1)) =
      ∫ τ in (0 : ℝ)..t, a 0 * (((e + 1 : ℕ) : ℝ) * τ ^ (e + 1 - 1)) := by
    refine intervalIntegral.integral_congr fun τ hτ => ?_
    rw [Set.uIcc_of_le ht.1] at hτ
    rw [ha τ ⟨hτ.1, hτ.2.trans ht.2⟩]
  rw [radialTransform, hint, integral_const_mul_dpow, ha t ht]
  ring

def RegRadialWeight.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (u : Fin n → ℂ) (ε : ℝ) (x : Fin n → ℂ) (a : ℝ → ℝ) (t₀ T : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    0 < ε → ContDiff ℝ ∞ a → 0 < t₀ → (∀ t ∈ Set.Icc 0 t₀, a t = a 0) → (∀ t, T ≤ t → a t = 0) →
    (∫ τ in (0 : ℝ)..T, a τ * ((d : ℝ) * τ ^ (d - 1))) = 0 →
      ∫ y, chartDens J A (fun z => a (euclPot (z - x))) (vecCons (logReg u ε) fun _ => euclPot) y =
        ∫ y, chartDens J A (fun z => radialTransform d a (euclPot (z - x)))
          (vecCons (logReg u ε) fun _ => logDistSq x) y

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCurveProperClosedFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

theorem CurveProperClosedFinite.no_chain_two {R : Type*} [CommRing R] {W P Q : Ideal R}
    (hW : W.IsPrime) (hP : P.IsPrime) (hQ : Q.IsPrime) (hdim : ringKrullDim (R ⧸ W) = 1)
    (hWP : W < P) (hPQ : P < Q) : False := by
  let a : PrimeSpectrum.zeroLocus (R := R) (W : Set R) :=
    ⟨⟨W, hW⟩, (PrimeSpectrum.mem_zeroLocus _ _).2 le_rfl⟩
  let b : PrimeSpectrum.zeroLocus (R := R) (W : Set R) :=
    ⟨⟨P, hP⟩, (PrimeSpectrum.mem_zeroLocus _ _).2 hWP.le⟩
  let c : PrimeSpectrum.zeroLocus (R := R) (W : Set R) :=
    ⟨⟨Q, hQ⟩, (PrimeSpectrum.mem_zeroLocus _ _).2 (hWP.trans hPQ).le⟩
  have hab : a < b := hWP
  have hbc : b < c := hPQ
  let p0 : LTSeries (PrimeSpectrum.zeroLocus (R := R) (W : Set R)) := RelSeries.singleton _ a
  have h2 := Order.LTSeries.length_le_krullDim ((p0.snoc b hab).snoc c hbc)
  rw [← ringKrullDim_quotient, hdim] at h2
  have hl : ((p0.snoc b hab).snoc c hbc).length = 2 := by
    rfl
  rw [hl] at h2
  norm_num at h2

theorem CurveProperClosedFinite.proof : CurveProperClosedFinite.Statement := by
  intro n W K hW hdim hK
  let m : (Fin n → ℂ) → Ideal (MvPolynomial (Fin n) ℂ) := fun x => RingHom.ker (eval x)
  have hinj : Function.Injective m := by
    intro x y hxy
    funext i
    have hx : X i - C (x i) ∈ m x := by simp [m, RingHom.mem_ker]
    have hy : X i - C (x i) ∈ m y := hxy ▸ hx
    have hy' : y i - x i = 0 := by simpa [m, RingHom.mem_ker] using hy
    exact (sub_eq_zero.1 hy').symm
  have hsub : m '' (zeroSet W ∩ zeroSet K) ⊆ (W ⊔ K).minimalPrimes := by
    rintro _ ⟨x, ⟨hxW, hxK⟩, rfl⟩
    have hmax : (m x).IsMaximal :=
      RingHom.ker_isMaximal_of_surjective (eval x) (fun c => ⟨C c, by simp⟩)
    have hle : W ⊔ K ≤ m x := sup_le (fun q hq => hxW q hq) (fun q hq => hxK q hq)
    refine ⟨⟨hmax.isPrime, hle⟩, fun Q ⟨hQ, hJQ⟩ hQm => ?_⟩
    by_contra hmQ
    have hWQ : W < Q := by
      refine lt_of_le_of_ne (le_sup_left.trans hJQ) ?_
      rintro rfl
      exact hK (le_sup_right.trans hJQ)
    exact CurveProperClosedFinite.no_chain_two hW hQ hmax.isPrime hdim hWQ (lt_of_le_of_ne hQm
      (fun h => hmQ (h ▸ le_rfl)))
  exact Set.Finite.of_finite_image
    ((Ideal.finite_minimalPrimes_of_isNoetherianRing _ _).subset hsub) hinj.injOn

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PointLocalRingOrder
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology

noncomputable section

variable {σ : Type*}

theorem pointLocalRing_exists_mul_eq (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (x : pointLocalRing I w) :
    ∃ a s : MvPolynomial σ ℂ, eval w s ≠ 0 ∧
      x * algebraMap (MvPolynomial σ ℂ) (pointLocalRing I w) s = algebraMap (MvPolynomial σ ℂ) (pointLocalRing I w) a := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective
    (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)).primeCompl y
  refine ⟨a, s, fun h ↦ s.2 (RingHom.mem_ker.2 h), ?_⟩
  have h := congrArg (Ideal.Quotient.mk (I.map (algebraMap (MvPolynomial σ ℂ)
    (Localization.AtPrime (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ))))))
    (IsLocalization.mk'_spec (Localization.AtPrime (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ))) a s)
  rw [map_mul] at h
  exact h

theorem pointLocalRing_exists_mul_mem (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (g : MvPolynomial σ ℂ)
    (hg : algebraMap (MvPolynomial σ ℂ) (pointLocalRing I w) g = 0) :
    ∃ s : MvPolynomial σ ℂ, eval w s ≠ 0 ∧ s * g ∈ I := by
  set p := RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)
  have hmem : algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime p) g ∈
      I.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime p)) :=
    Ideal.Quotient.eq_zero_iff_mem.1 hg
  obtain ⟨⟨j, s⟩, hjs⟩ := (IsLocalization.mem_map_algebraMap_iff p.primeCompl (Localization.AtPrime p)).1 hmem
  refine ⟨s, fun h ↦ s.2 (RingHom.mem_ker.2 h), ?_⟩
  have hinj := IsLocalization.injective (Localization.AtPrime p) p.primeCompl_le_nonZeroDivisors
  have : (s : MvPolynomial σ ℂ) * g = j := hinj (by rw [map_mul, mul_comm]; exact hjs)
  rw [this]
  exact j.2

theorem pointLocalRing_eval_ne_zero_of_isUnit (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ)
    (hw : w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn I) (u : MvPolynomial σ ℂ)
    (hu : IsUnit (algebraMap (MvPolynomial σ ℂ) (pointLocalRing I w) u)) : eval w u ≠ 0 := by
  intro h0
  set p := RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)
  have hle : I.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime p)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime p) := by
    rw [Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ _ g).2 (RingHom.mem_ker.2 (hw g hg))
  have hum : algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime p) u ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime p) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff _ _ u).2 (RingHom.mem_ker.2 h0)
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective v
  have hv' : Ideal.Quotient.mk (I.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime p)))
      (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime p) u * z) = Ideal.Quotient.mk _ 1 := by
    rw [map_mul, map_one]
    exact hv
  have hd := hle (Ideal.Quotient.eq.1 hv')
  have h1 : (1 : Localization.AtPrime p) ∈ IsLocalRing.maximalIdeal (Localization.AtPrime p) := by
    have := (IsLocalRing.maximalIdeal (Localization.AtPrime p)).sub_mem
      (Ideal.mul_mem_right z _ hum) hd
    simp at this
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem ord_zero_eq_top_of_dvr (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    Ring.ord R 0 = ⊤ := by
  rw [Ring.ord_zero]
  by_contra h
  have hfin := Module.length_ne_top_iff.1 h
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 hfin
  exact IsDiscreteValuationRing.not_isField R (IsArtinianRing.isField_of_isDomain R)

theorem ord_pow_irreducible_of_dvr {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {ϖ : R} (hϖ : Irreducible ϖ) (e : ℕ) : Ring.ord R (ϖ ^ e) = e := by
  rw [Ring.ord_pow (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero), Ring.ord_of_irreducible hϖ]
  simp

theorem differentiable_eval_pointLocal [Fintype σ] (q : MvPolynomial σ ℂ) :
    Differentiable ℂ fun z : σ → ℂ ↦ eval z q := by
  induction q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [eval_add]; exact hp.add hq
  | mul_X p i hp => simp only [eval_mul, eval_X]; exact hp.mul (differentiable_apply i)

theorem analyticAt_eval_disc [Fintype σ] {r : ℝ} (hr : 0 < r) {φ : (Fin 1 → ℂ) → σ → ℂ}
    (hφ : DifferentiableOn ℂ φ (Metric.ball 0 r)) (g : MvPolynomial σ ℂ) :
    AnalyticAt ℂ (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) g) 0 := by
  have hc : DifferentiableOn ℂ (fun τ : ℂ ↦ (fun _ : Fin 1 ↦ τ)) (Metric.ball 0 r) :=
    (differentiable_pi.2 fun _ ↦ differentiable_id).differentiableOn
  have hmaps : Set.MapsTo (fun τ : ℂ ↦ (fun _ : Fin 1 ↦ τ)) (Metric.ball 0 r) (Metric.ball 0 r) := by
    intro τ hτ
    rw [mem_ball_zero_iff] at hτ ⊢
    exact lt_of_le_of_lt (pi_norm_const_le τ) hτ
  have hd : DifferentiableOn ℂ (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) g) (Metric.ball 0 r) :=
    (differentiable_eval_pointLocal g).comp_differentiableOn (hφ.comp hc hmaps)
  exact hd.analyticAt (Metric.ball_mem_nhds 0 hr)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeSheetGramLintegral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix Filter Topology Set ComplexSets

open scoped ENNReal

noncomputable section

theorem IsSheetAt.eventuallyEq {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin d) (Fin n) ℂ} {x : Fin n → ℂ} {γ s : (Fin d → ℂ) → Fin n → ℂ}
    (hγ : IsSheetAt J A x γ) (hs : IsSheetAt J A x s) : γ =ᶠ[𝓝 (A *ᵥ x)] s := by
  obtain ⟨U, hU, hxU, hγd, hγx, hγZ, -⟩ := hγ
  obtain ⟨U', hU', hxU', -, -, -, V, hV, hsV⟩ := hs
  have hc : ContinuousAt γ (A *ᵥ x) := (hγd.differentiableAt (hU.mem_nhds hxU)).continuousAt
  have hV' : ∀ᶠ y in 𝓝 (A *ᵥ x), γ y ∈ V := hc.preimage_mem_nhds (by rwa [hγx])
  filter_upwards [hU.mem_nhds hxU, hU'.mem_nhds hxU', hV'] with y hy hy' hyV
  obtain ⟨hAy, hZy⟩ := hγZ y hy
  have h := hsV (γ y) ⟨hZy, hyV⟩ (by rwa [hAy])
  rwa [hAy] at h

theorem ConeSheetGramLintegral.proof (hPar : ConeSliceSheetParam.Statement)
    (hArea : ConeMapArea.Statement) : ConeSheetGramLintegral.Statement := by
  classical
  intro n e h J ℓ A F hJ hdim hℓ hA hF
  obtain ⟨U, D, N, s, hUD, hdisj, hnull, hfib, hinj, hsub, hcov⟩ := hPar n e h J ℓ A hJ hdim hℓ hA

  set v : (Σ k, Fin (N k)) → (Fin e → ℂ) → (Fin n → ℂ) :=
    fun i y => (h.matᵀ)⁻¹ *ᵥ s i.1 i.2 y with hv_def
  have hvd : ∀ i : Σ k, Fin (N k), DifferentiableOn ℂ (v i) (U i.1) := fun i =>
    (Matrix.mulVecLin (h.matᵀ)⁻¹).toContinuousLinearMap.differentiable.comp_differentiableOn
      ((hUD i.1).2.2.2 i.2)

  set H : (Σ k, Fin (N k)) → (Fin e → ℂ) → ℝ≥0∞ := fun i y =>
    ∫⁻ t : ℂ, F (t • WithLp.toLp 2 (v i y)) * ENNReal.ofReal (‖t‖ ^ (2 * e) * gramVol (v i) y)
    with hH_def
  have hHm : ∀ i : Σ k, Fin (N k), AEMeasurable (H i) (volume.restrict (D i.1)) := fun i =>
    aemeasurable_coneTerm (hUD i.1).1 (hUD i.1).2.2.1 (hvd i) hF

  set G : (Fin e → ℂ) → ℝ≥0∞ := fun y =>
    ∑ᶠ x ∈ ComplexSets.fibre (J ⊔ Ideal.span {linForm ℓ - 1}) A y, ∫⁻ t : ℂ,
      F (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A x y)) *
        ENNReal.ofReal (‖t‖ ^ (2 * e) * gramVol (fun y' =>
          (h.matᵀ)⁻¹ *ᵥ sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A x y') y) with hG_def

  have hGD : ∀ k, ∀ y ∈ D k, G y = ∑ j : Fin (N k), H ⟨k, j⟩ y := by
    intro k y hy
    obtain ⟨hfe, hinjy, hsh⟩ := hfib k y ((hUD k).2.2.1 hy)
    simp only [hG_def, hfe]
    rw [finsum_mem_range hinjy, finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hAy : A *ᵥ s k j y = y := by
      have hmem : s k j y ∈ ComplexSets.fibre (J ⊔ Ideal.span {linForm ℓ - 1}) A y := hfe ▸ ⟨j, rfl⟩
      exact hmem.2
    have hex : ∃ γ, IsSheetAt (J ⊔ Ideal.span {linForm ℓ - 1}) A (s k j y) γ := ⟨s k j, hsh j⟩
    have hch : sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A (s k j y) =ᶠ[𝓝 y] s k j := by
      have h1 : sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A (s k j y) = hex.choose := by
        simp only [sheetThrough, dif_pos hex]
      have h2 := hex.choose_spec.eventuallyEq (hsh j)
      rw [hAy] at h2
      rw [h1]
      exact h2
    have hval : sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A (s k j y) y = s k j y :=
      hch.eq_of_nhds
    have hgram : gramVol (fun y' =>
        (h.matᵀ)⁻¹ *ᵥ sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A (s k j y) y') y =
        gramVol (v ⟨k, j⟩) y :=
      gramVol_congr (hch.fun_comp fun f => (h.matᵀ)⁻¹ *ᵥ f)
    simp only [hH_def, hv_def, hval, hgram]

  set G' : (Fin e → ℂ) → ℝ≥0∞ := fun y =>
    ∑' k, (D k).indicator (fun y => ∑ j : Fin (N k), H ⟨k, j⟩ y) y with hG'_def
  have hGG' : G =ᵐ[volume] G' := by
    have hae : ∀ᵐ y ∂(volume : Measure (Fin e → ℂ)), y ∈ ⋃ k, D k := by
      rw [ae_iff]
      simpa [compl_def] using hnull
    filter_upwards [hae] with y hy
    obtain ⟨k, hk⟩ := mem_iUnion.1 hy
    simp only [hG'_def]
    rw [tsum_eq_single k, indicator_of_mem hk, hGD k y hk]
    intro k' hk'
    exact indicator_of_notMem (fun h' => (hdisj hk').le_bot ⟨h', hk⟩) _
  have hG'm : ∀ k, AEMeasurable ((D k).indicator fun y => ∑ j : Fin (N k), H ⟨k, j⟩ y) volume :=
    fun k => (aemeasurable_indicator_iff (hUD k).2.1).2
      (Finset.aemeasurable_fun_sum _ fun j _ => hHm ⟨k, j⟩)
  refine ⟨(AEMeasurable.tsum hG'm).congr hGG'.symm, ?_⟩

  have hRHS : ∫⁻ y, G y = ∑' i : Σ k, Fin (N k), ∫⁻ y in D i.1, H i y := by
    rw [lintegral_congr_ae hGG', lintegral_tsum hG'm, ENNReal.tsum_sigma']
    refine tsum_congr fun k => ?_
    rw [lintegral_indicator (hUD k).2.1, lintegral_finsetSum' _ fun j _ => hHm ⟨k, j⟩,
      tsum_fintype]

  have hLHS : ∫⁻ z in {z : EuclideanSpace ℂ (Fin n) | ∀ q ∈ J, eval (h.pointOf z) q = 0}, F z
        ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) =
      ∫⁻ z in (fun q : (Σ k, Fin (N k)) × (Fin e → ℂ) × ℂ => q.2.2 • WithLp.toLp 2 (v q.1 q.2.1)) ''
          {q | q.2.1 ∈ D q.1.1 ∧ q.2.2 ≠ 0}, F z
        ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) := by
    refine setLIntegral_congr (ae_eq_set.2 ⟨hcov, ?_⟩)
    rw [sdiff_eq_empty.2 hsub, measure_empty]
  have hMap := hArea n e (Σ k, Fin (N k)) (fun i => U i.1) (fun i => D i.1) v F
    (fun i => ⟨(hUD i.1).1, (hUD i.1).2.1, (hUD i.1).2.2.1, hvd i⟩) hinj hF
  rw [hLHS, hMap]
  exact congrArg _ hRHS.symm

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PChartMassCompact
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ENNReal

noncomputable section

namespace ChartMassCompact

variable {n d : ℕ}

theorem mdisc_coord_zero {D : ℕ} (M : Fin D → Matrix (Fin D) (Fin D) ℂ) (i : Fin D)
    (hi : M i = 0) : ReciprocityTheory.AnForm.mdisc M = 0 := by
  rw [ReciprocityTheory.AnForm.A.mdisc_eq_sum_polCoef]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun r _ => ?_)
  by_cases hr : Function.Surjective r
  · obtain ⟨j, hj⟩ := hr i
    refine mul_eq_zero_of_right _ (Matrix.det_eq_zero_of_row_eq_zero j fun k => ?_)
    simp [hj, hi]
  · rw [ReciprocityTheory.AnForm.A.polCoef_eq_zero r hr, zero_mul]

theorem hessC_eq_zero_of_eventuallyEq {D : ℕ} {φ : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}
    (h : φ =ᶠ[𝓝 z] 0) : ReciprocityTheory.AnForm.hessC φ z = 0 := by
  have h1 : fderiv ℝ φ =ᶠ[𝓝 z] fderiv ℝ (0 : (Fin D → ℂ) → ℝ) := h.fderiv
  have h2 : fderiv ℝ (fderiv ℝ φ) z = 0 := by
    rw [h1.fderiv_eq]
    simp
  ext i j
  simp [ReciprocityTheory.AnForm.hessC, h2]

theorem maDens_eq_zero {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {x : Fin n → ℂ} {s : (Fin d → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A x s)
    (ψ : Fin d → (Fin n → ℂ) → ℝ) (i : Fin d) (hx : x ∉ tsupport (ψ i)) :
    ReciprocityTheory.AnForm.maDens (fun k => ψ k ∘ s) (A *ᵥ x) = 0 := by
  obtain ⟨U, hU, hxU, hsd, hsx, -⟩ := hs
  have hcont : ContinuousAt s (A *ᵥ x) := (hsd.differentiableAt (hU.mem_nhds hxU)).continuousAt
  have hev : (ψ i ∘ s) =ᶠ[𝓝 (A *ᵥ x)] 0 := by
    have hnhds : (tsupport (ψ i))ᶜ ∈ 𝓝 (s (A *ᵥ x)) := by
      rw [hsx]
      exact (isClosed_tsupport _).isOpen_compl.mem_nhds hx
    filter_upwards [hcont.preimage_mem_nhds hnhds] with y hy
    show ψ i (s y) = 0
    exact image_eq_zero_of_notMem_tsupport hy
  unfold ReciprocityTheory.AnForm.maDens
  rw [mdisc_coord_zero _ i (hessC_eq_zero_of_eventuallyEq hev)]
  simp

theorem integrable_ball (hC : ChartMassCompare.Statement) (hMF : MassFinite.Statement)
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (ψ : Fin d → (Fin n → ℂ) → ℝ)
    (hJ : J.IsPrime) (hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d)
    (hA : IsFiniteProjection J A) (hψ : ∀ k, SmoothNear (zeroSet J) (ψ k)) (R : ℝ) :
    Integrable (chartAbsDens J A ((Metric.closedBall (0 : Fin n → ℂ) R).indicator fun _ => (1 : ℝ)) ψ) := by
  obtain ⟨K, hK, hle⟩ := hC n d J A ψ R hJ hd hA hψ
  have hmeas := (SheetSumMeasurable.proof n d J A
    ((Metric.closedBall (0 : Fin n → ℂ) R).indicator fun _ => (1 : ℝ)) ψ hJ hd hA
    (measurable_const.indicator Metric.isClosed_closedBall.measurableSet) hψ).2
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  have hbd : Bornology.IsBounded
      (WithLp.ofLp ⁻¹' Metric.closedBall (0 : Fin n → ℂ) R : Set (EuclideanSpace ℂ (Fin n))) :=
    (PiLp.antilipschitzWith_ofLp 2 fun _ : Fin n => ℂ).isBounded_preimage Metric.isBounded_closedBall
  obtain ⟨R', hR'⟩ := (Metric.isBounded_iff_subset_ball 0).1 hbd
  have h1 := hle (fun _ => 1) measurable_const
  simp only [enorm_one, setLIntegral_one] at h1
  refine h1.trans_lt (ENNReal.mul_lt_top hK ?_)
  exact (measure_mono (Set.inter_subset_inter_right _ hR')).trans_lt (hMF n d J hJ hd R')

theorem chartAbsDens_le (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (ψ : Fin d → (Fin n → ℂ) → ℝ) {K B : Set (Fin n → ℂ)} {M : ℝ}
    (hKB : K ⊆ B) (hM : ∀ x ∈ zeroSet J ∩ K, |f x| ≤ M) (hM0 : 0 ≤ M)
    (hvan : ∀ x s, IsSheetAt J A x s → x ∉ K →
      f x * ReciprocityTheory.AnForm.maDens (fun k => ψ k ∘ s) (A *ᵥ x) = 0)
    (y : Fin d → ℂ) (hfin : (ComplexSets.fibre J A y).Finite) :
    chartAbsDens J A f ψ y ≤ M * chartAbsDens J A (B.indicator fun _ => 1) ψ y := by
  classical
  unfold chartAbsDens sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun x hx => ?_
  rw [Set.Finite.mem_toFinset] at hx
  obtain ⟨hxZ, rfl⟩ := hx
  split_ifs with h
  · dsimp only
    by_cases hxK : x ∈ K
    · rw [Set.indicator_of_mem (hKB hxK), one_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right (hM x ⟨hxZ, hxK⟩) (abs_nonneg _)
    · rw [hvan x _ h.choose_spec hxK, abs_zero]
      positivity
  · simp

end ChartMassCompact


open ChartMassCompact in
theorem ChartMassCompact.proof (hC : ChartMassCompare.Statement) (hMF : MassFinite.Statement) :
    ChartMassCompact.Statement := by
  classical
  intro n d J A f ψ hJ hd hA hf hψ hsupp
  obtain ⟨K, hKc, hvan⟩ : ∃ K : Set (Fin n → ℂ), IsCompact K ∧ ∀ x s, IsSheetAt J A x s → x ∉ K →
      f x * ReciprocityTheory.AnForm.maDens (fun k => ψ k ∘ s) (A *ᵥ x) = 0 := by
    rcases hsupp with hc | ⟨i, hc⟩
    · exact ⟨tsupport f, hc, fun x s _ hx => by rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]⟩
    · exact ⟨tsupport (ψ i), hc, fun x s hs hx => by rw [maDens_eq_zero hs ψ i hx, mul_zero]⟩
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 hKc.isBounded
  obtain ⟨M, hM⟩ := (hKc.inter_left (SheetSumMeasurable.isClosed_zeroSet J)).exists_bound_of_continuousOn
    (hf.mono Set.inter_subset_left)
  have heq : chartAbsDens J A f ψ = chartAbsDens J A ((zeroSet J).piecewise f 0) ψ := by
    funext y
    unfold chartAbsDens sheetSum
    refine finsum_congr fun x => finsum_congr fun hx => ?_
    simp only [Set.piecewise_eq_of_mem _ _ _ hx.1]
  have hgm : Measurable ((zeroSet J).piecewise f 0) :=
    hf.measurable_piecewise continuousOn_const (SheetSumMeasurable.isClosed_zeroSet J).measurableSet
  have hmeas : AEStronglyMeasurable (chartAbsDens J A f ψ) volume := by
    rw [heq]
    exact (SheetSumMeasurable.proof n d J A _ ψ hJ hd hA hgm hψ).2.aestronglyMeasurable
  refine ((integrable_ball hC hMF J A ψ hJ hd hA hψ R).const_mul (max M 0)).mono' hmeas
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (chartAbsDens_nonneg _ _ _ _ _)]
  exact chartAbsDens_le J A f ψ hR (fun x hx => (Real.norm_eq_abs (f x) ▸ hM x hx).trans (le_max_left _ _))
    (le_max_right _ _) hvan y (FibreBound.proof n d J A hJ hd hA y).2.1

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMHeightAddDim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u

def CMHeightAddDim.Statement : Prop :=
  ∀ (B : Type u) [CommRing B] [IsCohenMacaulayLocalRing B] (J : Ideal B), J ≠ ⊤ →
    (J.height : WithBot ℕ∞) + ringKrullDim (B ⧸ J) = ringKrullDim B

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMHeightOneGeneral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

def CMHeightOneGeneral.Statement : Prop :=
  ∀ (n : ℕ) (J W : Ideal (MvPolynomial (Fin n) ℂ)) (g : MvPolynomial (Fin n) ℂ),
    J.IsPrime → g ∉ J → W ∈ (J ⊔ Ideal.span {g}).minimalPrimes →
      ∃ f : MvPolynomial (Fin n) ℂ, f ∉ W ∧ ∀ q ∈ zeroSet W, eval q f ≠ 0 → IsCohenMacaulayAt J q

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMGeneralPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

def CMGeneralPoint.Statement : Prop :=
  ∀ (n : ℕ) (I W : Ideal (MvPolynomial (Fin n) ℂ)), W ∈ I.minimalPrimes →
    ∃ f : MvPolynomial (Fin n) ℂ, f ∉ W ∧ ∀ q ∈ zeroSet W, eval q f ≠ 0 →
      (∀ W' ∈ I.minimalPrimes, q ∈ zeroSet W' → W' = W) ∧ IsCohenMacaulayAt I q

end GroundTheory.Heights₂.Heights
end
