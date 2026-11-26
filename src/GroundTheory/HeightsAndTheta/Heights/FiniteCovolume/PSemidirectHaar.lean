module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PComplementExtension
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsZsmulMem

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PSemidirectHaar
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

theorem SemidirectHaar.proof (G T : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] :
    SemidirectHaar.Statement G T := by
  intro P H hP hH hHP τ β δ hτ hβ hδc hτP _ hτH hβH μ _ ν _ ρ _ hδ
  have : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : LocallyCompactSpace P := hP.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology H := inferInstanceAs (SecondCountableTopology (H : Set G))
  have : SecondCountableTopology P := inferInstanceAs (SecondCountableTopology (P : Set G))

  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G)
  have hUo : IsOpen (interior K) := isOpen_interior
  have hU1 : (1 : G) ∈ interior K := mem_interior_iff_mem_nhds.2 hK1
  set f : G → ℝ≥0∞ := (interior K).indicator 1 with hf_def
  have hfm : Measurable f := measurable_one.indicator hUo.measurableSet
  have hI : ∫⁻ x : H, f x ∂ν = ν (Subtype.val ⁻¹' interior K) := by
    rw [← lintegral_indicator_one (hUo.preimage continuous_subtype_val).measurableSet]
    congr 1
  have hI0 : ∫⁻ x : H, f x ∂ν ≠ 0 := by
    rw [hI]
    exact ((hUo.preimage continuous_subtype_val).measure_pos ν ⟨1, hU1⟩).ne'
  have hItop : ∫⁻ x : H, f x ∂ν ≠ ∞ := by
    rw [hI]
    exact ((measure_mono (Set.preimage_mono interior_subset)).trans_lt
      (hH.isClosedEmbedding_subtypeVal.isCompact_preimage hK).measure_lt_top).ne

  have hmul : ∀ s t, δ (s * t) = δ s * δ t := by
    intro s t
    have e1 := hδ (s * t) f hfm
    have e2 : ∫⁻ x : H, f (τ s * (τ t * x * (τ t)⁻¹) * (τ s)⁻¹) ∂ν =
        δ t * ∫⁻ x : H, f (τ s * x * (τ s)⁻¹) ∂ν :=
      hδ t (fun z => f (τ s * z * (τ s)⁻¹))
        (hfm.comp ((continuous_const.mul continuous_id).mul continuous_const).measurable)
    have e3 := hδ s f hfm
    have e : ∫⁻ x : H, f (τ (s * t) * x * (τ (s * t))⁻¹) ∂ν =
        ∫⁻ x : H, f (τ s * (τ t * x * (τ t)⁻¹) * (τ s)⁻¹) ∂ν := by
      congr 1
      funext x
      simp only [map_mul, mul_inv_rev]
      group
    rw [e, e2, e3, ← mul_assoc] at e1
    have h := (ENNReal.mul_left_inj hI0 hItop).1 e1
    exact (ENNReal.coe_injective (by rw [ENNReal.coe_mul]; exact h)).symm.trans (mul_comm _ _)
  have hone : δ 1 = 1 := by
    have e := hδ 1 f hfm
    simp only [map_one, one_mul, inv_one, mul_one] at e
    have h := (ENNReal.mul_left_inj hI0 hItop).1 (e.symm.trans (one_mul _).symm)
    exact_mod_cast h
  have hpos : ∀ t, δ t ≠ 0 := fun t h => by
    have e := hmul t t⁻¹
    rw [mul_inv_cancel, hone, h, zero_mul] at e
    exact one_ne_zero e

  let Φ : T × H → P := fun q => ⟨(q.2 : G) * τ q.1, P.mul_mem (hHP q.2.2) (hτP q.1)⟩
  have hΦc : Continuous Φ :=
    ((continuous_subtype_val.comp continuous_snd).mul (hτ.comp continuous_fst)).subtype_mk _
  have hΦm : Measurable Φ := hΦc.measurable
  have hδm : Measurable fun t => (δ t : ℝ≥0∞) := (ENNReal.continuous_coe.comp hδc).measurable
  let m : Measure P := Measure.map Φ ((ρ.withDensity fun t => (δ t : ℝ≥0∞)).prod ν)
  have hm : ∀ ψ : P → ℝ≥0∞, Measurable ψ →
      ∫⁻ p, ψ p ∂m = ∫⁻ t, δ t * ∫⁻ x : H, ψ (Φ (t, x)) ∂ν ∂ρ := by
    intro ψ hψ
    rw [lintegral_map hψ hΦm, lintegral_prod (fun z => ψ (Φ z)) (hψ.comp hΦm).aemeasurable,
      lintegral_withDensity_eq_lintegral_mul _ hδm]
    · rfl
    · exact (hψ.comp hΦm).lintegral_prod_right'

  have hinv : ∀ (p₀ : P) (ψ : P → ℝ≥0∞), Measurable ψ →
      ∫⁻ p, ψ (p₀ * p) ∂m = ∫⁻ p, ψ p ∂m := by
    intro p₀ ψ hψ
    rw [hm (fun p => ψ (p₀ * p)) (hψ.comp (measurable_const_mul p₀)), hm _ hψ]
    set s := β p₀ with hs
    let y : H := ⟨(p₀ : G) * (τ s)⁻¹, hβH p₀⟩
    let ψ' : G → ℝ≥0∞ := Function.extend Subtype.val ψ 0
    have hψ' : Measurable ψ' :=
      (MeasurableEmbedding.subtype_coe hP.measurableSet).measurable_extend hψ measurable_const
    have hψ'e : ∀ p : P, ψ' p = ψ p := fun p => Subtype.val_injective.extend_apply ψ 0 p
    have inner : ∀ t, ∫⁻ x : H, ψ (p₀ * Φ (t, x)) ∂ν =
        δ s * ∫⁻ x : H, ψ (Φ (s * t, x)) ∂ν := by
      intro t
      have h1 : ∫⁻ x : H, ψ' ((y : G) * (τ s * x * (τ s)⁻¹) * τ (s * t)) ∂ν =
          δ s * ∫⁻ x : H, ψ' ((y : G) * x * τ (s * t)) ∂ν :=
        hδ s (fun z => ψ' ((y : G) * z * τ (s * t)))
          (hψ'.comp ((continuous_const.mul continuous_id).mul continuous_const).measurable)
      have h2 : ∫⁻ x : H, ψ' ((y : G) * x * τ (s * t)) ∂ν = ∫⁻ x : H, ψ (Φ (s * t, x)) ∂ν := by
        rw [← lintegral_mul_left_eq_self (μ := ν) (fun x : H => ψ (Φ (s * t, x))) y]
        congr 1
        funext x
        rw [← hψ'e]
        rfl
      rw [← h2, ← h1]
      congr 1
      funext x
      rw [← hψ'e]
      congr 1
      simp only [Φ, y, Subgroup.coe_mul, map_mul]
      group
    refine Eq.trans ?_ (lintegral_mul_left_eq_self (μ := ρ)
      (fun u => (δ u : ℝ≥0∞) * ∫⁻ x : H, ψ (Φ (u, x)) ∂ν) s)
    congr 1
    funext t
    rw [inner, hmul, ENNReal.coe_mul]
    ring
  have : Measure.IsMulLeftInvariant m := by
    constructor
    intro p₀
    ext S hS
    rw [Measure.map_apply (measurable_const_mul p₀) hS, ← lintegral_indicator_one hS,
      ← lintegral_indicator_one (measurable_const_mul p₀ hS)]
    exact hinv p₀ _ (measurable_one.indicator hS)

  have hβΦ : ∀ t (x : H), β (Φ (t, x)) = t := by
    intro t x
    have h := H.mul_mem (H.inv_mem x.2) (hβH (Φ (t, x)))
    have h' : τ (t * (β (Φ (t, x)))⁻¹) ∈ H := by
      simpa [Φ, map_mul, map_inv, mul_assoc] using h
    exact (mul_inv_eq_one.1 (hτH _ h')).symm
  let α : P → H := fun p => ⟨(p : G) * (τ (β p))⁻¹, hβH p⟩
  have hα : Continuous α :=
    (continuous_subtype_val.mul (hτ.comp hβ).inv).subtype_mk _
  have hαΦ : ∀ t (x : H), α (Φ (t, x)) = x := by
    intro t x
    apply Subtype.ext
    simp only [α, hβΦ]
    simp [Φ]
  have : IsFiniteMeasureOnCompacts m := by
    constructor
    intro K hK
    have hL : IsCompact (closure K) := hK.closure
    refine (measure_mono subset_closure).trans_lt ?_
    have hLm : MeasurableSet (closure K) := isClosed_closure.measurableSet
    obtain ⟨C, hC⟩ := (hL.image hβ).bddAbove_image hδc.continuousOn
    rw [← lintegral_indicator_one hLm, hm _ (measurable_one.indicator hLm)]
    calc ∫⁻ t, δ t * ∫⁻ x : H, (closure K).indicator 1 (Φ (t, x)) ∂ν ∂ρ
        ≤ ∫⁻ t, (β '' closure K).indicator (fun _ => (C : ℝ≥0∞) * ν (α '' closure K)) t ∂ρ := by
          refine lintegral_mono fun t => ?_
          by_cases ht : t ∈ β '' closure K
          · rw [Set.indicator_of_mem ht]
            gcongr
            · exact_mod_cast hC ⟨t, ht, rfl⟩
            · calc ∫⁻ x : H, (closure K).indicator 1 (Φ (t, x)) ∂ν
                  ≤ ∫⁻ x : H, (α '' closure K).indicator (fun _ => (1 : ℝ≥0∞)) x ∂ν := by
                    refine lintegral_mono fun x => ?_
                    by_cases hx : Φ (t, x) ∈ closure K
                    · rw [Set.indicator_of_mem hx,
                        Set.indicator_of_mem (show x ∈ α '' closure K from ⟨Φ (t, x), hx, hαΦ t x⟩)]
                      rfl
                    · rw [Set.indicator_of_notMem hx]
                      exact bot_le
                _ ≤ 1 * ν (α '' closure K) := lintegral_indicator_const_le _ _
                _ = ν (α '' closure K) := one_mul _
          · have h0 : ∀ x : H, (closure K).indicator (1 : P → ℝ≥0∞) (Φ (t, x)) = 0 :=
              fun x => Set.indicator_of_notMem (fun hx => ht ⟨Φ (t, x), hx, hβΦ t x⟩) _
            simp [h0]
      _ ≤ (C : ℝ≥0∞) * ν (α '' closure K) * ρ (β '' closure K) :=
          lintegral_indicator_const_le _ _
      _ < ∞ := ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top
          (hL.image hα).measure_lt_top) (hL.image hβ).measure_lt_top

  have hm0 : m ≠ 0 := by
    intro h0
    have e := hm (fun _ => 1) measurable_const
    rw [h0, lintegral_zero_measure] at e
    simp only [lintegral_const, one_mul] at e
    rw [lintegral_mul_const _ hδm] at e
    have hν : ν Set.univ ≠ 0 := isOpen_univ.measure_ne_zero ν Set.univ_nonempty
    have hρ : ∫⁻ t, (δ t : ℝ≥0∞) ∂ρ ≠ 0 := by
      rw [Ne, lintegral_eq_zero_iff hδm]
      intro h
      have hF : ∀ᵐ _t ∂ρ, False := h.mono fun t ht => hpos t (by simpa using ht)
      rw [Filter.eventually_false_iff_eq_bot, ae_eq_bot] at hF
      exact isOpen_univ.measure_ne_zero ρ Set.univ_nonempty (by rw [hF]; rfl)
    exact mul_ne_zero hρ hν e.symm

  have hsc := Measure.isMulLeftInvariant_eq_smul m μ
  set c₀ := Measure.haarScalarFactor m μ with hc₀
  have hc0 : c₀ ≠ 0 := by
    intro h
    apply hm0
    rw [hsc, h, zero_smul]
  refine ⟨c₀⁻¹, inv_ne_zero hc0, fun φ hφ => ?_⟩
  have key : ∫⁻ p, φ p ∂m = ∫⁻ t, δ t * ∫⁻ x : H, φ (x * τ t) ∂ν ∂ρ :=
    hm _ (hφ.comp continuous_subtype_val.measurable)
  rw [hsc, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul] at key
  rw [← key, ENNReal.coe_inv hc0, ← mul_assoc,
    ENNReal.inv_mul_cancel (by exact_mod_cast hc0) ENNReal.coe_ne_top, one_mul]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StUnipotentCentral
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def UnipotentCentral.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (D : ℕ) (La : AddSubgroup W) (x₀ w₀ : W), IsDIntegral h D La → x₀ ∈ La →
    IsHyperbolicPair h x₀ w₀ → ∀ K₁ : Set (InfinitePlace E → ι → ℂ), IsCompact K₁ →
    ∃ K : Set (InfinitePlace E → ι → ℂ), IsCompact K ∧ ∀ n : unipRadical h v x₀,
      (∃ t : InfinitePlace E → ℂ, unipCoord h v x₀ w₀ n - (fun w => t w • vecAt v x₀ w) ∈ K₁) →
      ∃ δ : unipRadical h v x₀, (δ : archUnitary h v) ∈ vecStabGroup h v La x₀ ∧
        unipCoord h v x₀ w₀ (δ * n) ∈ K

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StUnipotentHorizontal
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def UnipotentHorizontal.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (D : ℕ) (La : AddSubgroup W) (x₀ w₀ : W), IsDIntegral h D La → x₀ ∈ La →
    IsHyperbolicPair h x₀ w₀ →
    ∃ K : Set (InfinitePlace E → ι → ℂ), IsCompact K ∧ ∀ n : unipRadical h v x₀,
      ∃ δ : unipRadical h v x₀, (δ : archUnitary h v) ∈ vecStabGroup h v La x₀ ∧
        ∃ t : InfinitePlace E → ℂ,
          unipCoord h v x₀ w₀ (δ * n) - (fun w => t w • vecAt v x₀ w) ∈ K

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PLineEigenvalue
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [NumberField E]

def LineEigenvalue.coordRatio (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W)
    (i : InfinitePlace E → ι) (g : archUnitary h v) (w : InfinitePlace E) : ℂ :=
  ((((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w) (i w)) / vecAt v x₀ w (i w)


omit [NumberField E] in
theorem LineEigenvalue.continuous_coordRatio (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W)
    (i : InfinitePlace E → ι) (w : InfinitePlace E) :
    Continuous fun g : archUnitary h v => coordRatio h v x₀ i g w := by
  unfold coordRatio
  refine Continuous.div_const ?_ _
  exact (continuous_apply (i w)).comp
    ((Units.continuous_val.comp ((continuous_apply w).comp continuous_subtype_val)).matrix_mulVec
      continuous_const)


omit [NumberField E] in
theorem LineEigenvalue.mulVec_eq_coordRatio {h : HermitianForm F E W} {v : Basis ι E W} {x₀ : W}
    {i : InfinitePlace E → ι} (hi : ∀ w, vecAt v x₀ w (i w) ≠ 0) {g : archUnitary h v}
    (hg : g ∈ lineStab h v x₀) (w : InfinitePlace E) :
    ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w =
      coordRatio h v x₀ i g w • vecAt v x₀ w := by
  obtain ⟨c, hc⟩ := hg w
  have e : coordRatio h v x₀ i g w = c := by
    rw [coordRatio, hc, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self (hi w), mul_one]
  rw [e, hc]

theorem LineEigenvalue.coordRatio_ne_zero {h : HermitianForm F E W} {v : Basis ι E W} {x₀ : W}
    {i : InfinitePlace E → ι} (hi : ∀ w, vecAt v x₀ w (i w) ≠ 0) {g : archUnitary h v}
    (hg : g ∈ lineStab h v x₀) (w : InfinitePlace E) : coordRatio h v x₀ i g w ≠ 0 := by
  intro h0
  have e := mulVec_eq_coordRatio hi hg w
  rw [h0, zero_smul] at e
  apply hi w
  have hX : vecAt v x₀ w = (((((g : InfinitePlace E → GL ι ℂ) w)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) *ᵥ
      (((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w)) := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  rw [hX, e, Matrix.mulVec_zero, Pi.zero_apply]

theorem LineEigenvalue.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h1 : VecAtNeZero.Statement v) : LineEigenvalue.Statement h v := by
  intro x₀ hx₀
  have hne : ∀ w, ∃ j, vecAt v x₀ w j ≠ 0 := fun w => by
    simpa using Function.ne_iff.mp (h1 x₀ hx₀ w)
  choose i hi using hne
  refine ⟨fun p w => Units.mk0 (coordRatio h v x₀ i (p : archUnitary h v) w)
    (coordRatio_ne_zero hi p.2 w), ?_, fun p w => ?_⟩
  · refine continuous_pi fun w => Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact (continuous_coordRatio h v x₀ i w).comp continuous_subtype_val
    · simp only [Units.val_inv_eq_inv_val, Units.val_mk0]
      exact ((continuous_coordRatio h v x₀ i w).comp continuous_subtype_val).inv₀
        fun p => coordRatio_ne_zero hi p.2 w
  · rw [Units.val_mk0]
    exact mulVec_eq_coordRatio hi p.2 w

theorem LineEigenvalue.closed (h : HermitianForm F E W) (v : Basis ι E W) :
    LineEigenvalue.Statement h v :=
  LineEigenvalue.proof h v (VecAtNeZero.proof v)

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipRadicalOfRational
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem UnipRadicalOfRational.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    UnipRadicalOfRational.Statement h v := by
  classical
  intro x₀ γ hx hz
  have hγ : ∀ u : W, γ • u = (γ : W ≃ₗ[E] W) u := fun _ => rfl

  have key : ∃ y : W, ∀ u : W, ∃ a : E,
      γ • u = u + h.toSesq x₀ u • (γ • y - y) + a • x₀ := by
    by_cases hy : ∃ y, h.toSesq x₀ y = 1
    · obtain ⟨y, hy⟩ := hy
      refine ⟨y, fun u => ?_⟩
      obtain ⟨a, ha⟩ := hz (u - h.toSesq x₀ u • y)
        (by rw [map_sub, map_smul, smul_eq_mul, hy, mul_one, sub_self])
      have hs : γ • (u - h.toSesq x₀ u • y) = γ • u - h.toSesq x₀ u • (γ • y) := by
        simp only [hγ, map_sub, map_smul]
      rw [hs] at ha
      refine ⟨a, ?_⟩
      rw [smul_sub, sub_eq_iff_eq_add.mp ha]
      abel
    · refine ⟨0, fun u => ?_⟩
      have h0 : h.toSesq x₀ u = 0 := by
        by_contra hu
        exact hy ⟨(h.toSesq x₀ u)⁻¹ • u, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hu]⟩
      obtain ⟨a, ha⟩ := hz u h0
      exact ⟨a, by simp [ha]⟩
  obtain ⟨y, hy⟩ := key
  choose a ha using fun j => hy (v j)
  rw [mem_unipRadical]
  intro w
  set M : Matrix ι ι ℂ := (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w :
    Matrix ι ι ℂ) with hM
  have hvec : ∀ x : W, M *ᵥ vecAt v x w = vecAt v (γ • x) w := fun x =>
    congrFun (archEmbed_smul_vecAt h v γ x) w

  have hcol : ∀ i j, M i j = w.embedding (v.repr (γ • v j) i) := by
    intro i j
    have := congrFun (hvec (v j)) i
    simpa [vecAt, Basis.repr_self, Finsupp.single_apply, mulVec, dotProduct, apply_ite,
      eq_comm] using this
  refine ⟨by rw [hvec, hx], fun z hz0 => ?_⟩

  have hℓ : ∑ j, w.embedding (h.toSesq x₀ (v j)) * z j = 0 := by
    rw [← hz0]
    have hH : ∀ j, w.embedding (h.toSesq x₀ (v j)) =
        ∑ i, star (vecAt v x₀ w i) * gramAt h v w i j := by
      intro j
      rw [HermAtPlace.proof h v w x₀ (v j)]
      simp [vecAt, Basis.repr_self, Finsupp.single_apply, mulVec, dotProduct, apply_ite]
    simp only [hH, dotProduct, mulVec, Finset.mul_sum, Finset.sum_mul, Pi.star_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  refine ⟨∑ j, w.embedding (a j) * z j, ?_⟩
  funext i
  have hrow : (M *ᵥ z) i = ∑ j, (w.embedding (if i = j then 1 else 0) +
      w.embedding (h.toSesq x₀ (v j)) * w.embedding (v.repr (γ • y - y) i) +
      w.embedding (a j) * w.embedding (v.repr x₀ i)) * z j := by
    simp only [mulVec, dotProduct, hcol]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ha j]
    simp [Basis.repr_self, Finsupp.single_apply, eq_comm]
  rw [hrow]
  simp only [add_mul, Finset.sum_add_distrib]
  have e1 : ∑ j, w.embedding (if i = j then 1 else 0) * z j = z i := by
    simp [apply_ite]
  have e2 : ∑ j, w.embedding (h.toSesq x₀ (v j)) * w.embedding (v.repr (γ • y - y) i) * z j =
      w.embedding (v.repr (γ • y - y) i) * ∑ j, w.embedding (h.toSesq x₀ (v j)) * z j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have e3 : ∑ j, w.embedding (a j) * w.embedding (v.repr x₀ i) * z j =
      (∑ j, w.embedding (a j) * z j) * w.embedding (v.repr x₀ i) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e1, e2, e3, hℓ]
  simp [vecAt]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PComplementArchCocompact
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology

noncomputable section

namespace ComplementArchCocompact

section Lattice

variable {E : Type*} [Field E] [NumberField E] {W : Type*} [AddCommGroup W] [Module E W]

theorem exists_zsmul_mem {La : AddSubgroup W} (hL : IsLattice E La) (x : W) :
    ∃ d : ℤ, d ≠ 0 ∧ d • x ∈ La :=
  _root_.UpperTheory.Reformulated.B.ExistsZsmulMem.exists_zsmul_mem hL x

end Lattice

end ComplementArchCocompact

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace ComplementArchCocompact

def formAt (h : HermitianForm F E W) (v : Basis ι E W) (w : InfinitePlace E) (u : ι → ℂ) :
    (ι → ℂ) →ₗ[ℂ] ℂ where
  toFun z := star u ⬝ᵥ (gramAt h v w *ᵥ z)
  map_add' x y := by simp [Matrix.mulVec_add, dotProduct_add]
  map_smul' c x := by simp [Matrix.mulVec_smul, dotProduct_smul]

def projAt (h : HermitianForm F E W) (v : Basis ι E W) (x₀ w₀ : W) :
    (InfinitePlace E → ι → ℂ) →ₗ[ℂ] (InfinitePlace E → ι → ℂ) :=
  LinearMap.pi fun w => (LinearMap.id - (formAt h v w (vecAt v w₀ w)).smulRight (vecAt v x₀ w) -
    (formAt h v w (vecAt v x₀ w)).smulRight (vecAt v w₀ w)) ∘ₗ LinearMap.proj w

omit [NumberField F] [NumberField E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] [DecidableEq ι] in
theorem projAt_apply (h : HermitianForm F E W) (v : Basis ι E W) (x₀ w₀ : W)
    (Y : InfinitePlace E → ι → ℂ) (w : InfinitePlace E) :
    projAt h v x₀ w₀ Y w = Y w - (star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ Y w)) • vecAt v x₀ w -
      (star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ Y w)) • vecAt v w₀ w := rfl

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Fintype ι] [DecidableEq ι] in
theorem vecAt_smul_apply (v : Basis ι E W) (a : E) (x : W) (w : InfinitePlace E) :
    vecAt v (a • x) w = w.embedding a • vecAt v x w := by
  funext i; simp [vecAt]

theorem projAt_vecAt (h : HermitianForm F E W) (v : Basis ι E W) {x₀ w₀ : W}
    (hp : IsHyperbolicPair h x₀ w₀) (e : W) :
    projAt h v x₀ w₀ (vecAt v e) = vecAt v (ComplementExtension.proj hp e : W) := by
  funext w
  rw [projAt_apply, ← HermAtPlace.proof h v w w₀, ← HermAtPlace.proof h v w x₀,
    ComplementExtension.proj_apply]
  simp only [← vecAtHom_apply, map_sub, Pi.sub_apply]
  simp only [vecAtHom_apply, vecAt_smul_apply]

end ComplementArchCocompact


open ComplementArchCocompact in
theorem ComplementArchCocompact.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    ComplementArchCocompact.Statement h v := by
  classical
  intro La x₀ w₀ m hLa hp hm
  obtain ⟨hli, hdim⟩ := CoordEmbedBasis.proof E ι
  let b₀ := Pi.basis fun _ : ι => integralBasis E
  let Bs := basisOfLinearIndependentOfCardEqFinrank' _ hli
    (by rw [hdim, finrank_eq_card_basis b₀])
  let e : _ → W := fun k => v.equivFun.symm (b₀ k)
  have hBe : ∀ k, Bs k = vecAt v (e k) := by
    intro k
    rw [coe_basisOfLinearIndependentOfCardEqFinrank']
    funext w i
    rw [vecAt, coordEmbed_apply, ← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  let p : _ → W := fun k => (ComplementExtension.proj hp (e k) : W)
  choose d hd hdL using fun k => exists_zsmul_mem hLa (p k)
  let f : _ → W := fun k => m • d k • p k
  let D : _ → ℝ := fun k => (m : ℝ) * d k
  have hD : ∀ k, D k ≠ 0 := fun k =>
    mul_ne_zero (by exact_mod_cast hm.ne') (by exact_mod_cast hd k)
  have hf : ∀ k, vecAt v (f k) = D k • vecAt v (p k) := by
    intro k
    simp only [f, D, ← vecAtHom_apply, map_nsmul, map_zsmul]
    rw [mul_smul, Nat.cast_smul_eq_nsmul, Int.cast_smul_eq_zsmul]
  refine ⟨(fun t : _ → ℝ => ∑ k, t k • vecAt v (f k)) '' Set.Icc 0 1,
    isCompact_Icc.image (continuous_finsetSum _ fun k _ =>
      (continuous_apply k).smul continuous_const), fun Y hY => ?_⟩
  have hPY : projAt h v x₀ w₀ Y = Y := by
    funext w
    rw [projAt_apply, (hY w).1, (hY w).2, zero_smul, zero_smul, sub_zero, sub_zero]
  set s : _ → ℝ := fun k => Bs.repr Y k * (D k)⁻¹ with hs
  have hYs : Y = ∑ k, s k • vecAt v (f k) := by
    calc Y = (projAt h v x₀ w₀).restrictScalars ℝ (∑ k, Bs.repr Y k • Bs k) := by
          rw [Bs.sum_repr]; exact hPY.symm
      _ = ∑ k, Bs.repr Y k • vecAt v (p k) := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [map_sum, map_smul, LinearMap.restrictScalars_apply, hBe]
          exact Finset.sum_congr rfl fun k _ => by rw [projAt_vecAt]
      _ = _ := Finset.sum_congr rfl fun k _ => by
          rw [hf, smul_smul, hs, mul_assoc, inv_mul_cancel₀ (hD k), mul_one]
  refine ⟨∑ k, ⌊s k⌋ • f k, ?_, ⟨∑ k, ⌊s k⌋ • d k • p k, ?_, ?_⟩,
    ⟨fun k => Int.fract (s k), ⟨fun k => Int.fract_nonneg _, fun k => (Int.fract_lt_one _).le⟩, ?_⟩⟩
  · exact Submodule.sum_mem _ fun k _ =>
      zsmul_mem (nsmul_mem (zsmul_mem (ComplementExtension.proj hp (e k)).2 _) _) _
  · exact La.sum_mem fun k _ => La.zsmul_mem (hdL k) _
  · rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _
  · show ∑ k, Int.fract (s k) • vecAt v (f k) = Y - vecAt v (∑ k, ⌊s k⌋ • f k)
    conv_rhs => rw [hYs]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← vecAtHom_apply, map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul, vecAtHom_apply, ← Int.cast_smul_eq_zsmul ℝ, ← sub_smul, Int.self_sub_floor]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentCoordProper
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology

noncomputable section

namespace UnipotentCoordProper

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def unipVec (H : Matrix ι ι ℂ) (X W₀ u e : ι → ℂ) : ι → ℂ :=
  e + (star X ⬝ᵥ (H *ᵥ e)) • u - (star u ⬝ᵥ (H *ᵥ (e - (star X ⬝ᵥ (H *ᵥ e)) • W₀))) • X

def unipMat (H : Matrix ι ι ℂ) (X W₀ u : ι → ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => unipVec H X W₀ u (Pi.single j 1) i

theorem continuous_unipMat (H : Matrix ι ι ℂ) (X W₀ : ι → ℂ) :
    Continuous (unipMat H X W₀) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have hc : Continuous fun u => unipVec H X W₀ u (Pi.single j 1) := by
    unfold unipVec
    apply Continuous.sub
    · exact continuous_const.add (continuous_const_smul _)
    · exact (continuous_star.dotProduct continuous_const).smul continuous_const
  exact (continuous_apply i).comp hc

theorem eq_unipMat {H G : Matrix ι ι ℂ} {X W₀ : ι → ℂ} (hU : Gᴴ * H * G = H)
    (hX : G *ᵥ X = X) (hz : ∀ z, star X ⬝ᵥ (H *ᵥ z) = 0 → ∃ c : ℂ, G *ᵥ z = z + c • X)
    (hXW : star X ⬝ᵥ (H *ᵥ W₀) = 1) (hWX : star W₀ ⬝ᵥ (H *ᵥ X) = 1) :
    G = unipMat H X W₀ (G *ᵥ W₀ - W₀) := by
  have ip : ∀ a b, star (G *ᵥ a) ⬝ᵥ (H *ᵥ (G *ᵥ b)) = star a ⬝ᵥ (H *ᵥ b) := by
    intro a b
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hU]
  set u := G *ᵥ W₀ - W₀ with hu
  have huX : star u ⬝ᵥ (H *ᵥ X) = 0 := by
    have := ip W₀ X
    rw [hX] at this
    simp only [hu, star_sub, sub_dotProduct, this, sub_self]
  have key : ∀ e, G *ᵥ e = unipVec H X W₀ u e := by
    intro e
    set b := star X ⬝ᵥ (H *ᵥ e) with hb
    set z := e - b • W₀ with hzdef
    have hXz : star X ⬝ᵥ (H *ᵥ z) = 0 := by
      simp only [hzdef, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, hXW, smul_eq_mul,
        mul_one, b, sub_self]
    obtain ⟨c, hc⟩ := hz z hXz
    have hGW : G *ᵥ W₀ = W₀ + u := by rw [hu]; abel
    have hc' : c = -(star u ⬝ᵥ (H *ᵥ z)) := by
      have := ip W₀ z
      rw [hc, hGW] at this
      simp only [star_add, add_dotProduct, mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul,
        hWX, huX, smul_eq_mul] at this
      linear_combination this
    have he : e = z + b • W₀ := by rw [hzdef]; abel
    have : G *ᵥ e = z + c • X + b • (W₀ + u) := by
      rw [he, mulVec_add, mulVec_smul, hc, hGW]
    rw [this, hc']
    simp only [unipVec, ← hb, ← hzdef]
    rw [he]
    simp only [smul_add, neg_smul]
    abel
  ext i j
  rw [unipMat, of_apply, ← key, mulVec_single_one, col_apply]

end UnipotentCoordProper

open UnipotentCoordProper

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem UnipotentCoordProper.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    UnipotentCoordProper.Statement h v := by
  intro x₀ w₀ hp K hK
  have hherm := HermAtPlace.proof h v
  set H := gramAt h v
  set X := vecAt v x₀
  set W0 := vecAt v w₀
  have hXW : ∀ w, star (X w) ⬝ᵥ (H w *ᵥ W0 w) = 1 := fun w => by
    rw [← hherm, hp.2.2, map_one]
  have hWX : ∀ w, star (W0 w) ⬝ᵥ (H w *ᵥ X w) = 1 := fun w => by
    rw [← hherm, ← h.conj_toSesq, hp.2.2, map_one, map_one]
  have hHdet : ∀ w, IsUnit (H w).det := fun w => by
    simp only [H, gramAt]
    rw [show ((gram h.toSesq v).map w.embedding).det = w.embedding (gram h.toSesq v).det from
      (RingHom.map_det w.embedding _).symm]
    exact (isUnit_det_gram h v).map w.embedding
  set Φ : InfinitePlace E → (ι → ℂ) → Matrix ι ι ℂ := fun w => unipMat (H w) (X w) (W0 w)
  set Ψ : InfinitePlace E → (ι → ℂ) → Matrix ι ι ℂ := fun w u => (H w)⁻¹ * (Φ w u)ᴴ * H w
  have hΦc : ∀ w, Continuous (Φ w) := fun w => continuous_unipMat _ _ _
  have hΨc : ∀ w, Continuous (Ψ w) := fun w =>
    (continuous_const.matrix_mul (hΦc w).matrix_conjTranspose).matrix_mul continuous_const
  have key : ∀ (n : unipRadical h v x₀) (w : InfinitePlace E),
      (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) =
        Φ w (unipCoord h v x₀ w₀ n w) ∧
      (((((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) =
        Ψ w (unipCoord h v x₀ w₀ n w) := by
    intro n w
    set G : Matrix ι ι ℂ := (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)
    have hU : Gᴴ * H w * G = H w := (mem_archUnitary.mp (n : archUnitary h v).2) w
    have hG : G = Φ w (unipCoord h v x₀ w₀ n w) :=
      eq_unipMat hU ((n.2 w).1) ((n.2 w).2) (hXW w) (hWX w)
    refine ⟨hG, ?_⟩
    set Gi : Matrix ι ι ℂ :=
      (((((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ)
    have hGGi : G * Gi = 1 := Units.mul_inv _
    show Gi = (H w)⁻¹ * (Φ w (unipCoord h v x₀ w₀ n w))ᴴ * H w
    rw [← hG]
    calc Gi = (H w)⁻¹ * (Gᴴ * H w * G) * Gi := by
          rw [hU, Matrix.nonsing_inv_mul _ (hHdet w), Matrix.one_mul]
      _ = (H w)⁻¹ * Gᴴ * H w * (G * Gi) := by simp only [Matrix.mul_assoc]
      _ = (H w)⁻¹ * Gᴴ * H w := by rw [hGGi, Matrix.mul_one]
  set Kw : InfinitePlace E → Set (ι → ℂ) := fun w => (fun y => y w) '' K
  have hKw : ∀ w, IsCompact (Kw w) := fun w => hK.image (continuous_apply w)
  set C : InfinitePlace E → Set (GL ι ℂ) := fun w => Units.embedProduct (Matrix ι ι ℂ) ⁻¹'
    ((Φ w '' Kw w) ×ˢ (MulOpposite.unop ⁻¹' (Ψ w '' Kw w)))
  have hC : ∀ w, IsCompact (C w) := fun w =>
    Units.isClosedEmbedding_embedProduct.isCompact_preimage
      (((hKw w).image (hΦc w)).prod
        (MulOpposite.opHomeomorph.isCompact_preimage.mp ((hKw w).image (hΨc w))))
  have hS : IsClosed {n : unipRadical h v x₀ | unipCoord h v x₀ w₀ n ∈ K} :=
    hK.isClosed.preimage (continuous_unipCoord h v x₀ w₀)
  rw [Subtype.isCompact_iff, Subtype.isCompact_iff, Set.image_image]
  refine (isCompact_univ_pi hC).of_isClosed_subset ?_ ?_
  · rw [← Set.image_image]
    exact (isClosed_archUnitary h v).isClosedEmbedding_subtypeVal.isClosedMap _
      ((isClosed_unipRadical h v x₀).isClosedEmbedding_subtypeVal.isClosedMap _ hS)
  · rintro _ ⟨n, hn, rfl⟩ w -
    exact ⟨⟨_, ⟨_, hn, rfl⟩, (key n w).1.symm⟩, ⟨_, ⟨_, hn, rfl⟩, (key n w).2.symm⟩⟩

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PRationalUnipotent
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic
open scoped Pointwise

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

namespace RationalUnipotent

def unipMap (h : HermitianForm F E W) (x₀ y : W) (c : E) : W →ₗ[E] W where
  toFun x := x + (h.toSesq x₀ x * c - h.toSesq y x) • x₀ + h.toSesq x₀ x • y
  map_add' a b := by
    simp only [map_add (f := _)]
    module
  map_smul' r a := by
    simp only [map_smul, smul_eq_mul, RingHom.id_apply]
    module

omit [NumberField E] in
theorem unipMap_apply (h : HermitianForm F E W) (x₀ y : W) (c : E) (x : W) :
    unipMap h x₀ y c x = x + (h.toSesq x₀ x * c - h.toSesq y x) • x₀ + h.toSesq x₀ x • y := rfl


omit [NumberField E] in
theorem sesq_swap (h : HermitianForm F E W) (u v : W) :
    h.toSesq u v = conj F E (h.toSesq v u) :=
  (h.isSymm.eq v u).symm


omit [NumberField E] in
theorem sesq_smul_left (h : HermitianForm F E W) (r : E) (u v : W) :
    h.toSesq (r • u) v = conj F E r * h.toSesq u v := by
  rw [LinearMap.map_smulₛₗ₂]
  rfl

theorem unipMap_unipMap (h : HermitianForm F E W) {x₀ y : W} {c : E}
    (hx₀ : h.toSesq x₀ x₀ = 0) (hy : h.toSesq x₀ y = 0)
    (hc : c + conj F E c = -h.toSesq y y) (x : W) :
    unipMap h x₀ y c (unipMap h x₀ (-y) (conj F E c) x) = x := by
  have hy' : h.toSesq y x₀ = 0 := by rw [sesq_swap, hy, map_zero]
  simp only [unipMap_apply, map_add (f := _), map_smul, map_neg, LinearMap.neg_apply, hx₀, hy, hy']
  have key : h.toSesq x₀ x * conj F E c - -h.toSesq y x +
      (h.toSesq x₀ x * c - (h.toSesq y x + -(h.toSesq x₀ x * h.toSesq y y))) = 0 := by
    linear_combination h.toSesq x₀ x * hc
  linear_combination (norm := module) key • x₀

theorem sesq_unipMap (h : HermitianForm F E W) {x₀ y : W} {c : E}
    (hx₀ : h.toSesq x₀ x₀ = 0) (hy : h.toSesq x₀ y = 0)
    (hc : c + conj F E c = -h.toSesq y y) (x x' : W) :
    h.toSesq (unipMap h x₀ y c x) (unipMap h x₀ y c x') = h.toSesq x x' := by
  have hy' : h.toSesq y x₀ = 0 := by rw [sesq_swap, hy, map_zero]
  simp only [unipMap_apply, map_add (f := _), map_smul, smul_eq_mul, LinearMap.add_apply,
    sesq_smul_left, hx₀, hy, hy', map_sub, map_mul, mul_zero, add_zero]
  rw [sesq_swap h x x₀, sesq_swap h x y]
  linear_combination conj F E (h.toSesq x₀ x) * h.toSesq x₀ x' * hc

def unipElem (h : HermitianForm F E W) {x₀ y : W} {c : E}
    (hx₀ : h.toSesq x₀ x₀ = 0) (hy : h.toSesq x₀ y = 0)
    (hc : c + conj F E c = -h.toSesq y y) : h.unitaryGroup :=
  ⟨LinearEquiv.ofLinearMap (unipMap h x₀ y c) (unipMap h x₀ (-y) (conj F E c))
    (LinearMap.ext fun x => unipMap_unipMap h hx₀ hy hc x)
    (LinearMap.ext fun x => by
      have e := unipMap_unipMap h (y := -y) (c := conj F E c) hx₀
        (by rw [map_neg, hy, neg_zero])
        (by rw [conj_conj, add_comm, hc, map_neg, LinearMap.map_neg₂, neg_neg]) x
      rwa [neg_neg, conj_conj] at e),
    fun x x' => sesq_unipMap h hx₀ hy hc x x'⟩

theorem unipElem_smul (h : HermitianForm F E W) {x₀ y : W} {c : E}
    (hx₀ : h.toSesq x₀ x₀ = 0) (hy : h.toSesq x₀ y = 0)
    (hc : c + conj F E c = -h.toSesq y y) (x : W) :
    unipElem h hx₀ hy hc • x = unipMap h x₀ y c x := rfl

theorem unipElem_inv_smul (h : HermitianForm F E W) {x₀ y : W} {c : E}
    (hx₀ : h.toSesq x₀ x₀ = 0) (hy : h.toSesq x₀ y = 0)
    (hc : c + conj F E c = -h.toSesq y y) (x : W) :
    (unipElem h hx₀ hy hc)⁻¹ • x = unipMap h x₀ (-y) (conj F E c) x := rfl

theorem unipMap_mem (h : HermitianForm F E W) {La : AddSubgroup W}
    (hsm : ∀ (a : 𝓞 E) (x : W), x ∈ La → (a : E) • x ∈ La) (hint : IsIntegralOn h La)
    {x₀ y : W} {c : E} (hx₀ : x₀ ∈ La) (hy : y ∈ La) (hc : c ∈ integralClosure ℤ E)
    {x : W} (hx : x ∈ La) : unipMap h x₀ y c x ∈ La := by
  have smul_mem : ∀ {α : E} {v : W}, α ∈ integralClosure ℤ E → v ∈ La → α • v ∈ La :=
    fun {α} {v} hα hv => hsm ⟨α, hα⟩ v hv
  rw [unipMap_apply]
  refine add_mem (add_mem hx (smul_mem ?_ hx₀)) (smul_mem (hint x₀ hx₀ x hx) hy)
  exact sub_mem (mul_mem (hint x₀ hx₀ x hx) hc) (hint y hy x hx)


omit [NumberField E] in
theorem conj_mem_integralClosure {c : E} (hc : c ∈ integralClosure ℤ E) :
    conj F E c ∈ integralClosure ℤ E :=
  (mem_integralClosure_iff ℤ E).2
    (((mem_integralClosure_iff ℤ E).1 hc).map (conj F E).toAlgHom.toRingHom.toIntAlgHom)

end RationalUnipotent


open RationalUnipotent in
theorem RationalUnipotent.proof (h : HermitianForm F E W) : RationalUnipotent.Statement h := by
  intro D La x₀ w₀ hD hx₀ hp
  refine ⟨1, one_pos, ?_⟩
  rintro y c hyW ⟨z₁, hz₁, rfl⟩ ⟨a, rfl⟩ hc
  simp only [Nat.cast_one, one_mul, one_smul] at hyW hc ⊢
  obtain ⟨hxx, hww, hxw⟩ := hp
  have hyx : h.toSesq x₀ z₁ = 0 := (mem_hypComplement.1 hyW).1
  have hyw : h.toSesq w₀ z₁ = 0 := (mem_hypComplement.1 hyW).2
  have hzx : h.toSesq z₁ x₀ = 0 := by rw [sesq_swap, hyx, map_zero]
  have hzw : h.toSesq z₁ w₀ = 0 := by rw [sesq_swap, hyw, map_zero]
  have haI : (a : E) ∈ integralClosure ℤ E :=
    (mem_integralClosure_iff ℤ E).2 (RingOfIntegers.isIntegral_coe a)
  set γ := unipElem h hxx hyx hc with hγ
  refine ⟨γ, ?_, ?_, ?_, ?_⟩
  · rw [latticeStab, MulAction.mem_stabilizer_iff]
    ext v
    constructor
    · intro hv
      obtain ⟨u, hu, rfl⟩ := (AddSubgroup.mem_smul_pointwise_iff_exists v γ La).1 hv
      rw [hγ, unipElem_smul]
      exact unipMap_mem h hD.isLattice.smul_mem hD.integral hx₀ hz₁ haI hu
    · intro hv
      refine AddSubgroup.mem_pointwise_smul_iff_inv_smul_mem.2 ?_
      rw [hγ, unipElem_inv_smul]
      exact unipMap_mem h hD.isLattice.smul_mem hD.integral hx₀ (neg_mem hz₁)
        (conj_mem_integralClosure haI) hv
  · rw [hγ, unipElem_smul, unipMap_apply, hxx, hzx]
    simp
  · rw [hγ, unipElem_smul, unipMap_apply, hxw, hzw]
    simp only [one_mul, sub_zero, one_smul]
    abel
  · intro z hz
    rw [hγ, unipElem_smul, unipMap_apply, (mem_hypComplement.1 hz).1]
    simp only [zero_mul, zero_sub, zero_smul, add_zero, neg_smul]
    abel

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end
