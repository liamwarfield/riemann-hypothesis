module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolyCoeffVectorsLieInFiniteDimensionalSmooth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShapeIntegratedOperatorRangesPolynomial

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousExpGAndToMInv
namespace GlobalTheory.CompanionTheory.ExpOneParam

theorem continuous_expG_and_toM_inv :
    ∀ (n : ℕ) (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ), Formalism.REAL.inG ε Z →
      Continuous (fun t : ℝ => Formalism.REAL.expG ε Z t) ∧
        ∀ t : ℝ, Formalism.REAL.toM (Formalism.REAL.expG ε Z t)⁻¹ = NormedSpace.exp (-((t : ℂ) • Z)) := by
  intro n ε Z hZ
  obtain ⟨h0, hadd, hcont, -⟩ := Formalism.REAL.group_exponential_facts n ε Z hZ
  refine ⟨hcont, fun t => ?_⟩
  have hinv : (Formalism.REAL.expG ε Z t)⁻¹ = Formalism.REAL.expG ε Z (-t) := by
    refine inv_eq_of_mul_eq_one_left ?_
    rw [← hadd, neg_add_cancel, h0]
  rw [hinv, Formalism.REAL.toM_expG ε Z (-t) hZ, Complex.ofReal_neg, neg_smul]

end GlobalTheory.CompanionTheory.ExpOneParam
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarRinvUJ
open MeasureTheory

namespace GlobalTheory.CompanionTheory.HaarUJ

theorem haar_rinv_UJ : ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (Formalism.REAL.UJ ε)) [μ.IsHaarMeasure],
    μ.IsMulRightInvariant := by
  intro n ε μ _
  have hν : (Formalism.REAL.muG ε).IsMulRightInvariant := ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular n ε g⟩
  have hμ : μ = Measure.haarScalarFactor μ (Formalism.REAL.muG ε) • Formalism.REAL.muG ε :=
    Measure.isMulLeftInvariant_eq_smul μ (Formalism.REAL.muG ε)
  refine ⟨fun g => ?_⟩
  rw [hμ, Measure.map_smul, map_mul_right_eq_self]
  exact (continuous_id.mul continuous_const).aemeasurable

end GlobalTheory.CompanionTheory.HaarUJ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTraceSmul
noncomputable section

open MeasureTheory Filter Topology Set GlobalTheory.Orb GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open Formalism.REAL (UJ KG toM toMK muK expG inG)
open GlobalTheory.PsCo.Pc1
open scoped InnerProductSpace

namespace GlobalTheory.PsCo.Pc3

theorem shapeM_mono {n : ℕ} (ε : Fin n → Bool) {d d' : ℕ} (h : d ≤ d') : ShapeM ε d ≤ ShapeM ε d' :=
  Submodule.span_mono fun _ ⟨H, P, hH, hP, e⟩ => ⟨H, P, hH, hP.trans h, e⟩

theorem hasTrace_add' {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U]
    {S T : U →L[ℂ] U} {a b : ℂ} (hS : HasTrace S a) (hT : HasTrace T b) : HasTrace (S + T) (a + b) :=
  ⟨hS.1.add hT.1, by rw [trace_add hS.1 hT.1, hS.2, hT.2]⟩

theorem hasTrace_smul' {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U]
    {T : U →L[ℂ] U} {a : ℂ} (c : ℂ) (hT : HasTrace T a) : HasTrace (c • T) (c * a) :=
  ⟨hT.1.smul c, by rw [trace_smul, hT.2]⟩

theorem toM_mul' {n : ℕ} {ε : Fin n → Bool} (a b : UJ ε) : toM (a * b) = toM a * toM b := rfl

theorem trace_adBas (hSh : StShape) (hBD : StBasDeriv) (hUF : UFin) (hRS : RangeShape) (hTS : TraceSum)
    (hCD : ConjDeriv) {n : ℕ} (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (U : Type)
    [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U] (π : UJ ε →* (U →L[ℂ] U))
    (hπ : IsUnitaryRep π) (hirr : IsTopIrreducible π) (Z : Mat n) (H : ℝ → ℝ) (P : Poly n)
    (hZ : LieU ε Z) (hH : IsCutFn H) :
    HasTrace (repOp π μ fun g => adBas ε Z H P (toM g)) 0 := by
  have := GlobalTheory.CompanionTheory.HaarUJ.haar_rinv_UJ n ε μ
  have hZG : inG ε Z := (GlobalTheory.T.indefiniteUnitaryLieAlgebra_mem_iff_entries n ε Z).2 hZ
  obtain ⟨hxc, hxinv⟩ := GlobalTheory.CompanionTheory.ExpOneParam.continuous_expG_and_toM_inv n ε Z hZG
  obtain ⟨hadS, hder⟩ := hBD n ε Z H P hZ hH
  have hbS : bas ε H P ∈ ShapeM ε (P.totalDegree + 2) := Submodule.subset_span ⟨H, P, hH, by omega, rfl⟩
  obtain ⟨-, -, hac, hacs⟩ := hSh n ε _ _ hadS
  obtain ⟨-, -, hbc, hbcs⟩ := hSh n ε _ _ hbS
  obtain ⟨L, hLf, hLmem, hLd⟩ := hUF n ε U π hπ hirr (P.totalDegree + 2)
  have := hLf
  obtain ⟨-, hTr⟩ := hRS n ε μ U π hπ _ _ hadS
  obtain ⟨-, hAr⟩ := hRS n ε μ U π hπ _ _ hbS
  set fad : UJ ε → ℂ := fun g => adBas ε Z H P (toM g) with hfad
  set fb : UJ ε → ℂ := fun g => bas ε H P (toM g) with hfb
  set T := repOp π μ fad with hT
  set A := repOp π μ fb with hA
  set e := stdOrthonormalBasis ℂ L with he
  set x : ℝ → UJ ε := fun t => expG ε Z t with hx
  have hx0 : x 0 = 1 := by
    apply Subtype.ext
    apply Units.ext
    have := Formalism.REAL.toM_expG ε Z 0 hZG
    simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero] at this
    exact this
  have hconj : ∀ (s : ℝ) (g : UJ ε), toM ((x s)⁻¹ * g * x s) =
      NormedSpace.exp (-((s : ℂ) • Z)) * toM g * NormedSpace.exp ((s : ℂ) • Z) := fun s g => by
    rw [toM_mul', toM_mul', hxinv s, Formalism.REAL.toM_expG ε Z s hZG]
  have key : ∀ (y : UJ ε) (v u : U), ⟪v, π y u⟫_ℂ = ⟪π y⁻¹ v, u⟫_ℂ := fun y v u => by
    rw [hπ.inner_apply_left, inv_inv]
  set w : UJ ε → ℂ := fun g => ∑ j, ⟪(e j : U), π g (e j : U)⟫_ℂ with hw
  have hwc : Continuous w := continuous_finsetSum _ fun j _ => continuous_const.inner (hπ.continuous_apply _)

  have hsum : ∑ j, ⟪(e j : U), T (e j : U)⟫_ℂ = ∫ g, fad g * w g ∂μ := by
    have hint : ∀ j ∈ Finset.univ, Integrable (fun g => fad g * ⟪(e j : U), π g (e j : U)⟫_ℂ) μ := fun j _ =>
      (hac.mul (continuous_const.inner (hπ.continuous_apply _))).integrable_of_hasCompactSupport hacs.mul_right
    simp only [hT, hπ.inner_repOp hac hacs, hw, Finset.mul_sum]
    rw [integral_finsetSum _ hint]

  have hid : ∀ t : ℝ, ∑ j, ⟪(e j : U), π (x t) (A (π (x t)⁻¹ (e j : U)))⟫_ℂ =
      ∫ g, fb ((x t)⁻¹ * g * x t) * w g ∂μ := by
    intro t
    set y := x t
    have h1 : ∀ j, ⟪(e j : U), π y (A (π y⁻¹ (e j : U)))⟫_ℂ =
        ∫ g, fb g * ⟪(e j : U), π (y * g * y⁻¹) (e j : U)⟫_ℂ ∂μ := by
      intro j
      rw [key y, hA, hπ.inner_repOp hbc hbcs]
      refine integral_congr_ae (Eventually.of_forall fun g => ?_)
      simp only
      congr 1
      rw [map_mul, map_mul]
      show _ = ⟪(e j : U), π y (π g (π y⁻¹ (e j : U)))⟫_ℂ
      rw [key y]
    have hint : ∀ j ∈ Finset.univ, Integrable (fun g => fb g * ⟪(e j : U), π (y * g * y⁻¹) (e j : U)⟫_ℂ) μ :=
      fun j _ => (hbc.mul (continuous_const.inner ((hπ.continuous_apply _).comp (by fun_prop)))).integrable_of_hasCompactSupport
        hbcs.mul_right
    rw [Finset.sum_congr rfl fun j _ => h1 j, ← integral_finsetSum _ hint]
    have e2 : (fun g => ∑ j, fb g * ⟪(e j : U), π (y * g * y⁻¹) (e j : U)⟫_ℂ) =
        fun g => fb g * w (y * g * y⁻¹) := funext fun g => by simp only [hw, Finset.mul_sum]
    rw [e2]
    have e3 := integral_mul_right_eq_self (μ := μ) (fun g => fb (y⁻¹ * g) * w (y * (y⁻¹ * g) * y⁻¹)) y
    have e4 := integral_mul_left_eq_self (μ := μ) (fun g => fb g * w (y * g * y⁻¹)) y⁻¹
    rw [← e4, ← e3]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    simp only
    congr 2
    · group
    · group

  have h0 : π (x 0) = 1 := by rw [hx0, map_one]
  have hCD' := hCD U L (fun t => π (x t)) (fun t => π (x t)⁻¹) A h0
    (fun t v u => by
      rw [hπ.inner_apply_left, ← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        ContinuousLinearMap.one_apply])
    (fun t v u => (hπ.inner_apply_left _ v u).symm) (fun v hv => hLd v hv Z hZG)
    (fun u => hLmem _ (hAr u).1) (fun u => hLmem _ (hAr u).2)
  have hfun : (fun t => ∑ j, ⟪(stdOrthonormalBasis ℂ L j : U), π (x t) (A (π (x t)⁻¹
      (stdOrthonormalBasis ℂ L j : U)))⟫_ℂ) = fun t => ∫ g, fb ((x t)⁻¹ * g * x t) * w g ∂μ :=
    funext hid
  rw [hfun] at hCD'

  have hC : IsCompact ((fun p : ℝ × UJ ε => x p.1 * p.2 * (x p.1)⁻¹) '' (Icc (-1 : ℝ) 1 ×ˢ tsupport fad)) :=
    (isCompact_Icc.prod hacs.isCompact).image (by fun_prop)
  obtain ⟨χ, h1, -, hcs, -⟩ := exists_continuous_one_zero_of_isCompact hC isClosed_empty (disjoint_empty _)
  obtain ⟨M, hM⟩ := hacs.exists_bound_of_continuous hac
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 1)
  have keyb : ∀ u ∈ Icc (-1 : ℝ) 1, ∀ g, ‖fad ((x u)⁻¹ * g * x u) * w g‖ ≤ M * ‖(χ g : ℂ)‖ * ‖w g‖ := by
    intro u hu g
    rw [norm_mul]
    by_cases h : fad ((x u)⁻¹ * g * x u) = 0
    · rw [h, norm_zero, zero_mul]
      positivity
    · have hg : g ∈ (fun p : ℝ × UJ ε => x p.1 * p.2 * (x p.1)⁻¹) '' (Icc (-1 : ℝ) 1 ×ˢ tsupport fad) :=
        ⟨(u, (x u)⁻¹ * g * x u), ⟨hu, subset_tsupport fad h⟩, by simp only; group⟩
      have h2 : (χ g : ℂ) = 1 := by simp [h1 hg]
      rw [h2, norm_one, mul_one]
      exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
  have hχc : Continuous fun g => (χ g : ℂ) := Complex.continuous_ofReal.comp χ.continuous
  have hbint : Integrable (fun g => M * ‖(χ g : ℂ)‖ * ‖w g‖) μ := by
    refine (((hχc.norm.const_mul M).mul hwc.norm)).integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.mul_right ?_
    refine HasCompactSupport.mul_left ?_
    exact (hcs.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero).norm
  have hcontF : ∀ (f : UJ ε → ℂ), Continuous f → ∀ u, Continuous fun g => f ((x u)⁻¹ * g * x u) * w g :=
    fun f hf u => (hf.comp (by fun_prop)).mul hwc
  have hint := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun u g => fb ((x u)⁻¹ * g * x u) * w g) (F' := fun u g => fad ((x u)⁻¹ * g * x u) * w g)
    (x₀ := (0 : ℝ)) (s := Ioo (-1 : ℝ) 1) (bound := fun g => M * ‖(χ g : ℂ)‖ * ‖w g‖)
    (Ioo_mem_nhds (by norm_num) (by norm_num))
    (Eventually.of_forall fun u => (hcontF fb hbc u).aestronglyMeasurable)
    (by
      simp only [hx0, inv_one, one_mul, mul_one]
      exact (hbc.mul hwc).integrable_of_hasCompactSupport hbcs.mul_right)
    (hcontF fad hac 0).aestronglyMeasurable
    (.of_forall fun g u hu => keyb u (Ioo_subset_Icc_self hu) g) hbint
    (.of_forall fun g u _ => by
      have e5 : (fun v : ℝ => fb ((x v)⁻¹ * g * x v) * w g) =
          fun v : ℝ => bas ε H P (NormedSpace.exp (-((v : ℂ) • Z)) * toM g * NormedSpace.exp ((v : ℂ) • Z)) * w g :=
        funext fun v => by simp only [hfb, hconj]
      rw [e5]
      have e6 : fad ((x u)⁻¹ * g * x u) =
          adBas ε Z H P (NormedSpace.exp (-((u : ℂ) • Z)) * toM g * NormedSpace.exp ((u : ℂ) • Z)) := by
        simp only [hfad, hconj]
      rw [e6]
      exact (hder (toM g) u).mul_const (w g))
  have hzero : ∫ g, fad ((x 0)⁻¹ * g * x 0) * w g ∂μ = 0 := hint.2.unique hCD'
  simp only [hx0, inv_one, one_mul, mul_one] at hzero
  have hTL : ∀ u, T u ∈ L := fun u => hLmem _ (hTr u).1
  have := hTS U L T hTL
  rwa [hsum, hzero] at this

theorem stTrAd_of : StShape → StBasDeriv → UFin → RangeShape → TraceSum → ConjDeriv → StTrAd := by
  intro hSh hBD hUF hRS hTS hCD n ε μ _ U _ _ _ π hπ hirr φ hφ
  suffices h : (∃ d, φ ∈ ShapeM ε d) ∧ HasTrace (repOp π μ fun g => φ (toM g)) 0 from h.2
  induction hφ using Submodule.span_induction with
  | mem φ hmem =>
    obtain ⟨Z, H, P, hZ, hH, rfl⟩ := hmem
    exact ⟨⟨_, (hBD n ε Z H P hZ hH).1⟩, trace_adBas hSh hBD hUF hRS hTS hCD ε μ U π hπ hirr Z H P hZ hH⟩
  | zero =>
    refine ⟨⟨0, zero_mem _⟩, ?_⟩
    have h0 : IsRepOp π μ (fun g => (0 : Mat n → ℂ) (toM g)) 0 := fun v => by
      simp only [Pi.zero_apply, zero_smul, integral_zero, ContinuousLinearMap.zero_apply]
      exact ⟨integrable_zero _ _ _, trivial⟩
    rw [h0.repOp_eq]
    exact ⟨isTraceClass_zero, trace_zero⟩
  | add φ₁ φ₂ _ _ h₁ h₂ =>
    obtain ⟨⟨d₁, hd₁⟩, ht₁⟩ := h₁
    obtain ⟨⟨d₂, hd₂⟩, ht₂⟩ := h₂
    refine ⟨⟨max d₁ d₂, add_mem (shapeM_mono ε (le_max_left _ _) hd₁) (shapeM_mono ε (le_max_right _ _) hd₂)⟩, ?_⟩
    have o₁ := (hRS n ε μ U π hπ d₁ φ₁ hd₁).1
    have o₂ := (hRS n ε μ U π hπ d₂ φ₂ hd₂).1
    have hs : IsRepOp π μ (fun g => (φ₁ + φ₂) (toM g))
        (repOp π μ (fun g => φ₁ (toM g)) + repOp π μ (fun g => φ₂ (toM g))) := fun v => by
      refine ⟨?_, ?_⟩
      · refine ((o₁ v).1.add (o₂ v).1).congr (Eventually.of_forall fun g => ?_)
        simp only [Pi.add_apply, add_smul]
      · rw [ContinuousLinearMap.add_apply, (o₁ v).2, (o₂ v).2, ← integral_add (o₁ v).1 (o₂ v).1]
        simp only [Pi.add_apply, add_smul]
    rw [hs.repOp_eq]
    simpa using hasTrace_add' ht₁ ht₂
  | smul c φ _ h =>
    obtain ⟨⟨d, hd⟩, ht⟩ := h
    refine ⟨⟨d, Submodule.smul_mem _ c hd⟩, ?_⟩
    have o := (hRS n ε μ U π hπ d φ hd).1
    have hs : IsRepOp π μ (fun g => (c • φ) (toM g)) (c • repOp π μ (fun g => φ (toM g))) := fun v => by
      refine ⟨?_, ?_⟩
      · refine ((o v).1.smul c).congr (Eventually.of_forall fun g => ?_)
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul]
      · rw [ContinuousLinearMap.smul_apply, (o v).2, ← integral_smul]
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul]
    rw [hs.repOp_eq]
    simpa using hasTrace_smul' c ht

end GlobalTheory.PsCo.Pc3
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumInnerMulInnerProj
noncomputable section

open scoped InnerProductSpace

namespace GlobalTheory.Pc3

section
variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] (L : Submodule ℂ U)
  [FiniteDimensional ℂ L]

theorem sum_inner_mul_inner_proj [L.HasOrthogonalProjection] (a c : U) :
    ∑ j, ⟪a, (stdOrthonormalBasis ℂ L j : U)⟫_ℂ * ⟪(stdOrthonormalBasis ℂ L j : U), c⟫_ℂ =
      ⟪a, c⟫_ℂ - ⟪a - L.starProjection a, c - L.starProjection c⟫_ℂ := by
  set e := stdOrthonormalBasis ℂ L
  have h1 : ∀ j, ⟪a, (e j : U)⟫_ℂ = ⟪(⟨L.starProjection a, L.starProjection_apply_mem a⟩ : L), e j⟫_ℂ := by
    intro j
    rw [Submodule.coe_inner]
    have := L.inner_starProjection_left_eq_right a (e j : U)
    rw [this, L.starProjection_eq_self_iff.2 (e j).2]
  have h2 : ∀ j, ⟪(e j : U), c⟫_ℂ = ⟪e j, (⟨L.starProjection c, L.starProjection_apply_mem c⟩ : L)⟫_ℂ := by
    intro j
    rw [Submodule.coe_inner]
    have := L.inner_starProjection_left_eq_right (e j : U) c
    rw [← this, L.starProjection_eq_self_iff.2 (e j).2]
  simp_rw [h1, h2]
  rw [e.sum_inner_mul_inner, Submodule.coe_inner]
  simp only
  have ha := L.sub_starProjection_mem_orthogonal a
  have hc := L.sub_starProjection_mem_orthogonal c
  have o1 : ⟪L.starProjection a, c - L.starProjection c⟫_ℂ = 0 :=
    Submodule.inner_right_of_mem_orthogonal (L.starProjection_apply_mem a) hc
  have o2 : ⟪a - L.starProjection a, L.starProjection c⟫_ℂ = 0 :=
    Submodule.inner_left_of_mem_orthogonal (L.starProjection_apply_mem c) ha
  have e1 : ⟪a, c⟫_ℂ = ⟪L.starProjection a + (a - L.starProjection a),
      L.starProjection c + (c - L.starProjection c)⟫_ℂ := by simp
  rw [e1, inner_add_left, inner_add_right, inner_add_right, o1, o2]
  ring

end

theorem conjDeriv : ∀ (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U] (L : Submodule ℂ U) [FiniteDimensional ℂ L] (x y : ℝ → U →L[ℂ] U) (A : U →L[ℂ] U), x 0 = 1 → (∀ t v w, inner ℂ (x t v) (x t w) = inner ℂ v w) → (∀ t v w, inner ℂ v (y t w) = inner ℂ (x t v) w) → (∀ v ∈ L, ∃ w, HasDerivAt (fun t => x t v) w 0) → (∀ u, A u ∈ L) → (∀ u, ContinuousLinearMap.adjoint A u ∈ L) → HasDerivAt (fun t => ∑ j, inner ℂ (stdOrthonormalBasis ℂ L j : U) (x t (A (y t (stdOrthonormalBasis ℂ L j : U))))) 0 0 := by
  intro U _ _ _ L _ x y A hx0 hxi hy hxd hA hAd
  set e := stdOrthonormalBasis ℂ L
  set E : Fin (Module.finrank ℂ L) → U := fun j => (e j : U)
  set b : Fin (Module.finrank ℂ L) → U := fun k => ContinuousLinearMap.adjoint A (E k)

  have hexp : ∀ u, A u = ∑ k, ⟪E k, A u⟫_ℂ • E k := by
    intro u
    have := e.sum_repr' (⟨A u, hA u⟩ : L)
    have h := congrArg (fun z : L => (z : U)) this
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at h
    exact h.symm
  have hterm : ∀ t, (∑ j, ⟪E j, x t (A (y t (E j)))⟫_ℂ) =
      ∑ k, (⟪x t (b k), x t (E k)⟫_ℂ - ⟪x t (b k) - L.starProjection (x t (b k)),
        x t (E k) - L.starProjection (x t (E k))⟫_ℂ) := by
    intro t
    have h1 : ∀ j, ⟪E j, x t (A (y t (E j)))⟫_ℂ = ∑ k, ⟪x t (b k), E j⟫_ℂ * ⟪E j, x t (E k)⟫_ℂ := by
      intro j
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hexp (y t (E j)), map_sum, inner_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, inner_smul_right, ← ContinuousLinearMap.adjoint_inner_left, hy]
    simp_rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact sum_inner_mul_inner_proj L _ _
  have hconst : ∀ t k, ⟪x t (b k), x t (E k)⟫_ℂ = ⟪b k, E k⟫_ℂ := fun t k => hxi t _ _
  simp_rw [hconst] at hterm
  have hfun : (fun t => ∑ j, ⟪E j, x t (A (y t (E j)))⟫_ℂ) = fun t =>
      (∑ k, ⟪b k, E k⟫_ℂ) - ∑ k, ⟪x t (b k) - L.starProjection (x t (b k)),
        x t (E k) - L.starProjection (x t (E k))⟫_ℂ := by
    funext t; rw [hterm t, Finset.sum_sub_distrib]
  show HasDerivAt (fun t => ∑ j, ⟪E j, x t (A (y t (E j)))⟫_ℂ) 0 0
  rw [hfun]
  have hbL : ∀ k, b k ∈ L := fun k => hAd _
  have hEL : ∀ k, E k ∈ L := fun k => (e k).2
  have hd : ∀ v ∈ L, ∃ w, HasDerivAt (fun t => x t v - L.starProjection (x t v)) w 0 ∧
      x 0 v - L.starProjection (x 0 v) = 0 := by
    intro v hv
    obtain ⟨w, hw⟩ := hxd v hv
    have hP : HasDerivAt (fun t => L.starProjection (x t v)) (L.starProjection w) 0 :=
      (L.starProjection.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hw
    refine ⟨w - L.starProjection w, hw.sub hP, ?_⟩
    rw [hx0, ContinuousLinearMap.one_apply, L.starProjection_eq_self_iff.2 hv, sub_self]
  have hsum : HasDerivAt (fun t => ∑ k, ⟪x t (b k) - L.starProjection (x t (b k)),
      x t (E k) - L.starProjection (x t (E k))⟫_ℂ) 0 0 := by
    have : (0 : ℂ) = ∑ _k : Fin (Module.finrank ℂ L), (0 : ℂ) := by simp
    rw [this]
    refine HasDerivAt.fun_sum fun k _ => ?_
    obtain ⟨w1, h1, z1⟩ := hd _ (hbL k)
    obtain ⟨w2, h2, z2⟩ := hd _ (hEL k)
    have := h1.inner ℂ h2
    rw [z1, z2, inner_zero_left, inner_zero_right, add_zero] at this
    exact this
  have := hsum.const_sub (∑ k, ⟪b k, E k⟫_ℂ)
  rwa [neg_zero] at this

end GlobalTheory.Pc3
end
end

namespace GlobalTheory.PsCo.Pc3

theorem stTrAd : GlobalTheory.PsCo.Pc1.StTrAd :=
  stTrAd_of
    GlobalTheory.ShapeSmoothFinite.stShape
    GlobalTheory.PsCo.Pc1.B.cutoffPolynomial_conjugation_deriv_mem_shapeSpan
    uFin rangeShape
    GlobalTheory.OpTrace.hasTrace_sum_inner_of_range_le
    GlobalTheory.Pc3.conjDeriv

end GlobalTheory.PsCo.Pc3
