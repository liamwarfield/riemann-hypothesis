module

public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ScalarOfMultOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesComplementUnitaryActsOnTerms
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedVectorDifferentiable
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedVectorDifferentiable
open MeasureTheory NumberField Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open Filter Topology
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.GardingVec

theorem hasDerivAt_orbit {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ]
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (ρ : G → H →L[ℂ] H) (w : H) (hmul : ∀ a b, ρ (a * b) w = ρ a (ρ b w))
    (hc : Continuous fun y => ρ y w) (a : G → ℂ) (ha : Continuous a) (hs : HasCompactSupport a)
    (hw : ∫ y, a y • ρ y w ∂μ = w) (e : ℝ → G) (he : Continuous e) (he0 : e 0 = 1)
    (D : ℝ → G → ℂ) (hD : Continuous fun p : ℝ × G => D p.1 p.2)
    (hd : ∀ s y, HasDerivAt (fun t => a ((e t)⁻¹ * y)) (D s y) s) :
    HasDerivAt (fun s => ρ (e s) w) (∫ y in tsupport a, D 0 y • ρ y w ∂μ) 0 := by
  have hint : Integrable (fun y => a y • ρ y w) μ :=
    (ha.smul hc).integrable_of_hasCompactSupport hs.smul_right
  have hform : (fun s => ρ (e s) w) = fun s => ∫ y, a ((e s)⁻¹ * y) • ρ y w ∂μ := by
    funext s
    rw [← integral_mul_left_eq_self (fun y => a ((e s)⁻¹ * y) • ρ y w) (e s)]
    conv_lhs => rw [← hw]
    rw [← ContinuousLinearMap.integral_comp_comm _ hint]
    simp only [inv_mul_cancel_left, hmul, map_smul]
  have hzero : ∀ s y, (e s)⁻¹ * y ∉ tsupport a → D s y = 0 := by
    intro s y hy
    have h1 : ∀ᶠ t in 𝓝 s, (e t)⁻¹ * y ∈ (tsupport a)ᶜ :=
      (he.inv.mul continuous_const).continuousAt.preimage_mem_nhds
        ((isClosed_tsupport a).isOpen_compl.mem_nhds hy)
    have h2 : HasDerivAt (fun t => a ((e t)⁻¹ * y)) 0 s :=
      (hasDerivAt_const s (0 : ℂ)).congr_of_eventuallyEq
        (h1.mono fun t ht => image_eq_zero_of_notMem_tsupport ht)
    exact (hd s y).unique h2
  have hK : IsCompact ((fun p : ℝ × G => e p.1 * p.2) '' (Set.Icc (-1) 1 ×ˢ tsupport a)) :=
    (isCompact_Icc.prod hs.isCompact).image ((he.comp continuous_fst).mul continuous_snd)
  set K := (fun p : ℝ × G => e p.1 * p.2) '' (Set.Icc (-1) 1 ×ˢ tsupport a) with hKdef
  have hcD : Continuous fun p : ℝ × G => D p.1 p.2 • ρ p.2 w := hD.smul (hc.comp continuous_snd)
  obtain ⟨M, hM⟩ := ((isCompact_Icc (a := (-1 : ℝ)) (b := 1)).prod hK).exists_bound_of_continuousOn
    hcD.continuousOn
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (𝕜 := ℝ)
    (F := fun s y => a ((e s)⁻¹ * y) • ρ y w) (F' := fun s y => D s y • ρ y w) (x₀ := 0)
    (bound := K.indicator fun _ => M) (s := Set.Icc (-1) 1) (Icc_mem_nhds (by norm_num) (by norm_num))
    (Eventually.of_forall fun s =>
      ((ha.comp (continuous_const.mul continuous_id)).smul hc).aestronglyMeasurable)
    (by simpa [he0] using hint)
    (hcD.comp (Continuous.prodMk_right 0)).aestronglyMeasurable
    (Eventually.of_forall fun y s hs' => by
      by_cases hy : y ∈ K
      · rw [Set.indicator_of_mem hy]; exact hM (s, y) ⟨hs', hy⟩
      · rw [Set.indicator_of_notMem hy, hzero s y, zero_smul, norm_zero]
        intro h
        exact hy ⟨(s, (e s)⁻¹ * y), ⟨hs', h⟩, by simp⟩)
    ((integrable_indicator_iff hK.isClosed.measurableSet).2 (integrableOn_const hK.measure_lt_top.ne))
    (Eventually.of_forall fun y s _ => (hd s y).smul_const _)
  rw [hform, setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact key.2
  · intro y hy
    rw [hzero 0 y (by simpa [he0] using hy), zero_smul]

theorem decay_setIntegral {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ρ : G → H →L[ℂ] H) (w : H) (hmul : ∀ a b, ρ (a * b) w = ρ a (ρ b w))
    (hc : Continuous fun y => ρ y w) {K : Set G} (hK : IsCompact K) (φ : G → ℂ) (hφ : Continuous φ)
    (d : G → ℝ) (hd : Continuous d) (hsub : ∀ a b, d (a * b) ≤ d a + d b) (c : ℝ) (hc0 : 0 ≤ c) (v : H)
    (h : ∃ C : ℝ, ∀ g, ‖⟪v, ρ g w⟫_ℂ‖ ≤ C * Real.exp (-(c * d g))) :
    ∃ C : ℝ, ∀ g, ‖⟪v, ρ g (∫ y in K, φ y • ρ y w ∂μ)⟫_ℂ‖ ≤ C * Real.exp (-(c * d g)) := by
  obtain ⟨C, hC⟩ := h
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 1)
    exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    (f := fun y => ‖φ y‖ * Real.exp (c * d y⁻¹))
    (hφ.norm.mul (Real.continuous_exp.comp (continuous_const.mul (hd.comp continuous_inv)))).continuousOn
  have hint : IntegrableOn (fun y => φ y • ρ y w) K μ :=
    (hφ.smul hc).continuousOn.integrableOn_compact hK
  refine ⟨C * M * μ.real K, fun g => ?_⟩
  have e1 : ⟪v, ρ g (∫ y in K, φ y • ρ y w ∂μ)⟫_ℂ = ∫ y in K, φ y * ⟪v, ρ (g * y) w⟫_ℂ ∂μ := by
    have := ContinuousLinearMap.integral_comp_comm ((innerSL ℂ v).comp (ρ g)) hint
    simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, map_smul, smul_eq_mul] at this
    simp only [hmul, this]
  rw [e1]
  refine (norm_setIntegral_le_of_norm_le_const (C := C * M * Real.exp (-(c * d g)))
    hK.measure_lt_top fun y hy => ?_).trans (le_of_eq (by ring))
  have h1 : d g ≤ d (g * y) + d y⁻¹ := by simpa using hsub (g * y) y⁻¹
  have h2 : Real.exp (-(c * d (g * y))) ≤ Real.exp (c * d y⁻¹) * Real.exp (-(c * d g)) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.2; nlinarith
  have h3 : ‖φ y‖ * Real.exp (c * d y⁻¹) ≤ M := (le_abs_self _).trans (hM y hy)
  rw [norm_mul]
  calc ‖φ y‖ * ‖⟪v, ρ (g * y) w⟫_ℂ‖
      ≤ ‖φ y‖ * (C * (Real.exp (c * d y⁻¹) * Real.exp (-(c * d g)))) :=
        mul_le_mul_of_nonneg_left ((hC _).trans (mul_le_mul_of_nonneg_left h2 hC0)) (norm_nonneg _)
    _ = C * (‖φ y‖ * Real.exp (c * d y⁻¹)) * Real.exp (-(c * d g)) := by ring
    _ ≤ _ := by gcongr

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
  Matrix.linftyOpNormedSpace

theorem tendsto_slope_exp {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) :
    Tendsto (slope (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) s) (𝓝[≠] s)
      (𝓝 (NormedSpace.exp ((s : ℂ) • X) * X)) := by
  have h := (hasDerivAt_exp_smul_const (𝕂 := ℂ) X ((s : ℝ) : ℂ))
  have h2 := h.scomp (x := s) Complex.ofRealCLM.hasDerivAt
  have h3 : HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X))
      (NormedSpace.exp ((s : ℂ) • X) * X) s := h2.congr_deriv (by rw [Complex.ofRealCLM_apply, Complex.ofReal_one, one_smul]; rfl)
  exact h3.tendsto_slope

theorem continuous_exp_curve {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) :=
  NormedSpace.exp_continuous.comp (Complex.continuous_ofReal.smul continuous_const)

end

theorem hasDerivAt_exp_mul {n : ℕ} (X y : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) :
    HasDerivAt (F := Fin n → Fin n → ℂ) (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X) * y : Matrix _ _ ℂ))
      (NormedSpace.exp ((s : ℂ) • X) * X * y : Matrix _ _ ℂ) s := by
  refine (hasDerivAt_iff_tendsto_slope (F := Fin n → Fin n → ℂ)).mpr ?_
  have h := (tendsto_slope_exp X s).mul_const y
  refine h.congr (fun t => ?_)
  have : ∀ f : ℝ → Matrix (Fin n) (Fin n) ℂ, slope f s t * y = slope (fun t => f t * y) s t := by
    intro f
    simp only [slope_def_module, Matrix.sub_mul, Matrix.smul_mul]
  exact this _

theorem fixed_vector_differentiable : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (α : Matrix (Fin n) (Fin n) ℂ → ℂ) (w : H), IsURepOn (UJset ε) σ → SmoothOnG ε α → HasCompactSupport (fun g : UJ ε => α (umat g)) → (∀ u : H, ∫ g : UJ ε, α (umat g) * ⟪u, σ (umat g) w⟫_ℂ ∂(muG ε) = ⟪u, w⟫_ℂ) → ∃ L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] H, ∀ X, inG ε X → HasDerivAt (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • X)) w) (L X) 0 ∧ ∀ (c : ℝ) (v : H), 0 ≤ c → (∃ C : ℝ, ∀ g : UJ ε, ‖⟪v, σ (umat g) w⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g)))) → (∃ C : ℝ, ∀ g : UJ ε, ‖⟪v, σ (umat g) (L X)⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g)))) := by
  intro n ε H _ _ _ σ α w hσ hα hs hw
  obtain ⟨F, hF, hFα⟩ := smoothOnG_exists_contDiff_extension n ε α hα
  have hu : Continuous fun g : UJ ε => umat g := (isClosedEmbeddingMatrix n ε).1.continuous
  have hmem : ∀ g : UJ ε, umat g ∈ UJset ε := fun g => g.2
  have hum : ∀ a b : UJ ε, umat (a * b) = umat a * umat b := fun _ _ => rfl
  have hmul : ∀ a b : UJ ε, σ (umat (a * b)) w = σ (umat a) (σ (umat b) w) := by
    intro a b
    rw [hum, hσ.1.2 _ (hmem a) _ (hmem b)]; rfl
  have hc : Continuous fun y : UJ ε => σ (umat y) w := (hσ.2.2 w).comp_continuous hu hmem
  have hFα' : ∀ g : UJ ε, α (umat g) = F (umat g) := fun g => (hFα _ g.2).symm
  have ha : Continuous fun g : UJ ε => α (umat g) := by
    simp only [hFα']; exact hF.continuous.comp hu
  have hint : Integrable (fun y : UJ ε => α (umat y) • σ (umat y) w) (muG ε) :=
    (ha.smul hc).integrable_of_hasCompactSupport hs.smul_right
  have hw' : ∫ y : UJ ε, α (umat y) • σ (umat y) w ∂(muG ε) = w := by
    refine ext_inner_left ℂ fun u => ?_
    rw [← integral_inner hint, ← hw u]
    simp only [inner_smul_right]
  have hfd : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by simp)
  let φ : Matrix (Fin n) (Fin n) ℂ → UJ ε → ℂ := fun X y =>
    fderiv ℝ F (umat y) ((-X) * umat y : Matrix _ _ ℂ)
  have hφ : ∀ X, Continuous (φ X) := fun X =>
    (hfd.comp hu).clm_apply (continuous_const.matrix_mul hu)
  have hφi : ∀ X, IntegrableOn (fun y => φ X y • σ (umat y) w)
      (tsupport fun g : UJ ε => α (umat g)) (muG ε) := fun X =>
    ((hφ X).smul hc).continuousOn.integrableOn_compact hs.isCompact
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] H :=
    { toFun := fun X => ∫ y in tsupport fun g : UJ ε => α (umat g), φ X y • σ (umat y) w ∂(muG ε)
      map_add' := fun X Y => by
        rw [← integral_add (hφi X) (hφi Y)]
        congr 1; funext y
        rw [← add_smul]
        congr 1
        have : (-(X + Y) * umat y : Matrix _ _ ℂ) = -X * umat y + -Y * umat y := by
          rw [neg_add, Matrix.add_mul]
        simp only [φ, this]
        exact (fderiv ℝ F (umat y)).map_add _ _
      map_smul' := fun r X => by
        rw [RingHom.id_apply, ← integral_smul]
        congr 1; funext y
        rw [← smul_assoc]
        congr 1
        have : (-(r • X) * umat y : Matrix _ _ ℂ) = r • (-X * umat y) := by
          rw [← smul_neg, Matrix.smul_mul]
        simp only [φ, this]
        exact (fderiv ℝ F (umat y)).map_smul _ _ }
  refine ⟨L, fun X hX => ⟨?_, fun c v hc0 h => ?_⟩⟩
  · let e : ℝ → UJ ε := fun t =>
      ⟨(Matrix.isUnit_exp ((t : ℂ) • X)).unit, exp_indefinite_unitary_holds n ε X hX t⟩
    have hev : ∀ t, umat (e t) = NormedSpace.exp ((t : ℂ) • X) := fun t => rfl
    have hei : ∀ t, umat (e t)⁻¹ = NormedSpace.exp ((t : ℂ) • (-X)) := fun t => by
      rw [smul_neg, Matrix.exp_neg, ← hev]
      exact Matrix.coe_units_inv _
    have he : Continuous e := by
      rw [(isClosedEmbeddingMatrix n ε).1.isInducing.continuous_iff]
      exact continuous_exp_curve X
    have he0 : e 0 = 1 := by
      apply Subtype.ext; apply Units.ext
      show umat (e 0) = 1
      rw [hev]; simp
    have hcE := continuous_exp_curve (-X)
    have key := hasDerivAt_orbit (muG ε) (fun g => σ (umat g)) w hmul hc _ ha hs hw' e he he0
      (fun s y => fderiv ℝ F (NormedSpace.exp ((s : ℂ) • (-X)) * umat y : Matrix _ _ ℂ)
        (NormedSpace.exp ((s : ℂ) • (-X)) * (-X) * umat y : Matrix _ _ ℂ))
      ((hfd.comp ((hcE.comp continuous_fst).matrix_mul (hu.comp continuous_snd))).clm_apply
        (((hcE.comp continuous_fst).matrix_mul continuous_const).matrix_mul (hu.comp continuous_snd)))
      (fun s y => by
        simp only [hFα']
        simp only [hum, hei]
        exact ((hF.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt s
          (hasDerivAt_exp_mul (-X) (umat y) s))
    simp only [hev, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.one_mul] at key
    exact key
  · exact decay_setIntegral (muG ε) (fun g => σ (umat g)) w hmul hc hs.isCompact (φ X) (hφ X)
      (fun g => dOp (umat g)) ((dFacts_holds n ε).2.1.comp_continuous hu hmem)
      (fun a b => ((dFacts_holds n ε).1 _ (hmem a)).2.2.1 _ (hmem b)) c hc0 v h

end GlobalTheory.GardingVec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedVectorDifferentiableStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_orbit_and_decay_of_decay : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (α : Matrix (Fin n) (Fin n) ℂ → ℂ) (w : H), IsURepOn (UJset ε) σ → SmoothOnG ε α → HasCompactSupport (fun g : UJ ε => α (umat g)) → (∀ u : H, ∫ g : UJ ε, α (umat g) * ⟪u, σ (umat g) w⟫_ℂ ∂(muG ε) = ⟪u, w⟫_ℂ) → ∃ L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] H, ∀ X, inG ε X → HasDerivAt (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • X)) w) (L X) 0 ∧ ∀ (c : ℝ) (v : H), 0 ≤ c → (∃ C : ℝ, ∀ g : UJ ε, ‖⟪v, σ (umat g) w⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g)))) → (∃ C : ℝ, ∀ g : UJ ε, ‖⟪v, σ (umat g) (L X)⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g)))) := by
  first | exact @GlobalTheory.GardingVec.fixed_vector_differentiable | exact GlobalTheory.GardingVec.fixed_vector_differentiable | (intros; apply GlobalTheory.GardingVec.fixed_vector_differentiable <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingMulVec
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.GramVol

theorem det_gram_contraction_le : ∀ (r : ℕ) (V W : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] (T : V →ₗ[ℂ] W), (∀ x, ‖T x‖ ≤ ‖x‖) → ∀ a : Fin r → V,
    ‖(Matrix.gram ℂ fun b => T (a b)).det‖ ≤ ‖(Matrix.gram ℂ a).det‖ := by
  intro r
  induction r with
  | zero => intro V W _ _ _ _ T _ a; simp
  | succ r ih =>
    intro V W _ _ _ _ T hT a
    have dec : ∀ (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] (v x : U),
        ∃ c : ℂ, x = c • v + (ℂ ∙ v)ᗮ.starProjection x := by
      intro U _ _ v x
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 ((ℂ ∙ v).starProjection_apply_mem x)
      exact ⟨c, by rw [hc]; exact ((ℂ ∙ v).starProjection_add_starProjection_orthogonal x).symm⟩
    have orth : ∀ (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] (v x : U),
        inner ℂ v ((ℂ ∙ v)ᗮ.starProjection x) = 0 := by
      intro U _ _ v x
      exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 ((ℂ ∙ v)ᗮ.starProjection_apply_mem x)
    choose c hc using fun b : Fin r => dec V (a 0) (a b.succ)
    set w : Fin r → V := fun b => (ℂ ∙ a 0)ᗮ.starProjection (a b.succ) with hw
    choose c' hc' using fun b : Fin r => dec W (T (a 0)) (T (w b))
    let T' : V →ₗ[ℂ] W := ((ℂ ∙ T (a 0))ᗮ.starProjection : W →L[ℂ] W).toLinearMap ∘ₗ T
    have hT' : ∀ x, ‖T' x‖ ≤ ‖x‖ := fun x =>
      le_trans ((ℂ ∙ T (a 0))ᗮ.norm_starProjection_apply_le (T x)) (hT x)
    have e1 : a = Fin.cons (a 0) (fun b => c b • a 0 + w b) := by
      funext i
      refine Fin.cases rfl (fun b => ?_) i
      simp only [Fin.cons_succ]
      exact hc b
    have e2 : (fun b => T (a b)) = Fin.cons (T (a 0)) (fun b => (c b + c' b) • T (a 0) + T' (w b)) := by
      funext i
      refine Fin.cases rfl (fun b => ?_) i
      simp only [Fin.cons_succ]
      have h1 : a b.succ = c b • a 0 + w b := hc b
      have h2 : T (w b) = c' b • T (a 0) + T' (w b) := hc' b
      rw [h1, map_add (f := _), map_smul, add_smul, add_assoc, ← h2]
    have g1 := Formalism.HermitianLatticeCounting.P.s5b7_gram_cons r (a 0) c w (fun b => orth V _ _)
    have g2 := Formalism.HermitianLatticeCounting.P.s5b7_gram_cons r (T (a 0)) (fun b => c b + c' b) (fun b => T' (w b))
      (fun b => orth W _ _)
    rw [← e1] at g1
    rw [← e2] at g2
    rw [g1, g2, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Complex.norm_real, norm_norm, norm_norm]
    have := ih V W T' hT' w
    have := hT (a 0)
    gcongr

theorem measurePreserving_mulVec {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (h : ‖g.det‖ = 1) :
    MeasurePreserving (fun x : Fin n → ℂ => g *ᵥ x) volume volume := by
  have hdet : LinearMap.det ((Matrix.toLin' g).restrictScalars ℝ) = 1 := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply,
      Complex.normSq_eq_norm_sq, h]; norm_num
  have h1 := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Fin n → ℂ))
    (f := (Matrix.toLin' g).restrictScalars ℝ) (by rw [hdet]; exact one_ne_zero)
  rw [hdet] at h1
  simp only [inv_one, abs_one, ENNReal.ofReal_one, one_smul] at h1
  refine ⟨?_, h1⟩
  exact (LinearMap.continuous_of_finiteDimensional ((Matrix.toLin' g).restrictScalars ℝ)).measurable

theorem exists_iso (d c : ℕ) (P : Submodule ℂ (EuclideanSpace ℂ (Fin (d + c)))) (hP : d ≤ Module.finrank ℂ P) :
    ∃ Φ : EuclideanSpace ℂ (Fin (d + c)) ≃ₗᵢ[ℂ] WithLp 2 (EuclideanSpace ℂ (Fin d) × EuclideanSpace ℂ (Fin c)),
      ∀ x, (Φ (P.starProjection x)).ofLp.1 = (Φ x).ofLp.1 := by
  obtain ⟨u, hu⟩ := exists_linearIndependent_of_le_finrank hP
  have hu' : LinearIndependent ℂ (P.subtype ∘ u) := hu.map' _ (Submodule.ker_subtype P)
  set K : Submodule ℂ (EuclideanSpace ℂ (Fin (d + c))) := Submodule.span ℂ (Set.range (P.subtype ∘ u)) with hK
  have hKP : K ≤ P := by
    rw [hK, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (u i).2
  have hKd : Module.finrank ℂ K = d := by
    rw [hK, finrank_span_eq_card hu']; simp
  have hKc : Module.finrank ℂ Kᗮ = c := by
    have := K.finrank_add_finrank_orthogonal
    rw [hKd, finrank_euclideanSpace, Fintype.card_fin] at this
    omega
  let e1 : K ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin d) := ((stdOrthonormalBasis ℂ K).reindex (finCongr hKd)).repr
  let e2 : Kᗮ ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin c) := ((stdOrthonormalBasis ℂ Kᗮ).reindex (finCongr hKc)).repr
  refine ⟨K.orthogonalDecomposition.trans (LinearIsometryEquiv.withLpProdCongr 2 e1 e2), fun x => ?_⟩
  have : ∀ y, ((K.orthogonalDecomposition.trans (LinearIsometryEquiv.withLpProdCongr 2 e1 e2)) y).ofLp.1 =
      e1 (K.orthogonalProjectionOnto y) := by
    intro y
    rw [← Submodule.fst_orthogonalDecomposition_apply]
    rfl
  rw [this, this]
  congr 1
  exact Submodule.orthogonalProjectionOnto_starProjection_of_le hKP x

theorem eucl_eq {n : ℕ} (v : Fin n → ℂ) : eucl v = ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin n))‖ := by
  rw [EuclideanSpace.norm_eq, eucl]
  simp only [Complex.normSq_eq_norm_sq]

theorem vol_le (d c j : ℕ) (hj : j ≤ d) (g : Matrix (Fin (d + c)) (Fin (d + c)) ℂ) (hg : ‖g.det‖ = 1)
    (P : Submodule ℂ (EuclideanSpace ℂ (Fin (d + c)))) (hP : d ≤ Module.finrank ℂ P) (R t : ℝ) (hR : 0 < R)
    (ht : 0 ≤ t) :
    volume {B : Fin j → Fin (d + c) → ℂ | (∀ b, eucl (g *ᵥ B b) ≤ R) ∧ gramProj P (fun b => g *ᵥ B b) ≤ t} ≤
      ENNReal.ofReal ((t ^ (2 * (d - j)) * R ^ (2 * j ^ 2) * Real.pi ^ (j * d) / ((d - j).factorial : ℝ) ^ j) *
        (Real.pi * R ^ 2) ^ (c * j)) := by
  obtain ⟨Φ, hΦ⟩ := exists_iso d c P hP
  have h0 : MeasurePreserving
      (Φ : EuclideanSpace ℂ (Fin (d + c)) → WithLp 2 (EuclideanSpace ℂ (Fin d) × EuclideanSpace ℂ (Fin c))) :=
    LinearIsometryEquiv.measurePreserving
      ({ (Φ.toLinearEquiv.restrictScalars ℝ) with norm_map' := Φ.norm_map } :
        EuclideanSpace ℂ (Fin (d + c)) ≃ₗᵢ[ℝ] WithLp 2 (EuclideanSpace ℂ (Fin d) × EuclideanSpace ℂ (Fin c)))
  have hl : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin (d + c) → ℂ)).symm :=
    GlobalTheory.volume_preserving_ofLp_complex (Fin (d + c))
  have hl' : MeasurePreserving (WithLp.toLp 2 : (Fin (d + c) → ℂ) → EuclideanSpace ℂ (Fin (d + c))) := hl.symm
  have h1 := h0.comp (hl'.comp (measurePreserving_mulVec g hg))
  have h2 : MeasurePreserving (Prod.map (id : EuclideanSpace ℂ (Fin d) → _) (@WithLp.ofLp 2 (Fin c → ℂ)))
      volume volume := (MeasurePreserving.id volume).prod (GlobalTheory.volume_preserving_ofLp_complex (Fin c))
  have h3 := h2.comp (WithLp.volume_preserving_ofLp (EuclideanSpace ℂ (Fin d)) (EuclideanSpace ℂ (Fin c)))
  have h4 := Formalism.HermitianLatticeCounting.P.measurePreserving_pi_comp_prod j _ _ h1 h3
  set S : Set ((Fin j → EuclideanSpace ℂ (Fin d)) × (Fin j → Fin c → ℂ)) :=
    Formalism.HermitianLatticeCounting.P.s5b7_A R d j t ×ˢ
      (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) R) with hS
  have hSm : MeasurableSet S :=
    (Formalism.HermitianLatticeCounting.P.s5b7_A_closed _ _ _ _).measurableSet.prod
      (MeasurableSet.univ_pi fun _ => MeasurableSet.univ_pi fun _ => Metric.isClosed_closedBall.measurableSet)
  have hball : volume (Set.pi Set.univ fun _ : Fin j => Set.pi Set.univ fun _ : Fin c => Metric.closedBall (0 : ℂ) R) =
      ENNReal.ofReal ((Real.pi * R ^ 2) ^ (c * j)) := by
    rw [volume_pi_pi]
    simp only [volume_pi_pi, Complex.volume_closedBall, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    rw [← pow_mul, ENNReal.ofReal_pow (by positivity), mul_comm Real.pi, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow hR.le]
    congr 2
    exact (ENNReal.ofReal_coe_nnreal (p := NNReal.pi)).symm
  refine le_trans (measure_mono ?_) (le_trans (h4.measure_preimage hSm.nullMeasurableSet).le ?_)
  · rintro B ⟨hB1, hB2⟩
    obtain ⟨v, hv⟩ : ∃ v : Fin j → EuclideanSpace ℂ (Fin (d + c)), v = fun b => WithLp.toLp 2 (g *ᵥ B b) := ⟨_, rfl⟩
    have hn : ∀ b, ‖Φ (v b)‖ ≤ R := fun b => by
      rw [Φ.norm_map, hv, ← eucl_eq]; exact hB1 b
    have hB3 : Real.sqrt ‖(Matrix.gram ℂ fun b => P.starProjection (v b)).det‖ ≤ t := by
      rw [hv]; exact hB2
    have goal : ((fun b => (Φ (v b)).ofLp.1, fun b => (Φ (v b)).ofLp.2.ofLp) :
        (Fin j → EuclideanSpace ℂ (Fin d)) × (Fin j → Fin c → ℂ)) ∈ S := by
      refine ⟨⟨fun b => ?_, ?_⟩, fun b _ i _ => ?_⟩
      · exact le_trans (WithLp.norm_fst_le _ _) (hn b)
      · refine le_trans (Real.sqrt_le_sqrt ?_) hB3
        obtain ⟨T, hT0⟩ : ∃ T : EuclideanSpace ℂ (Fin (d + c)) →ₗ[ℂ] EuclideanSpace ℂ (Fin d),
            ∀ x, T x = (Φ x).ofLp.1 :=
          ⟨(WithLp.fstL 2 ℂ _ _).toLinearMap ∘ₗ Φ.toLinearEquiv.toLinearMap, fun _ => rfl⟩
        have hT : ∀ x, ‖T x‖ ≤ ‖x‖ := fun x => by
          rw [hT0]; exact le_trans (WithLp.norm_fst_le _ (Φ x)) (Φ.norm_map x).le
        have := det_gram_contraction_le j _ _ T hT (fun b => P.starProjection (v b))
        simp only [hT0, hΦ] at this
        exact this
      · rw [mem_closedBall_zero_iff]
        exact le_trans (PiLp.norm_apply_le (Φ (v b)).ofLp.2 i)
          (le_trans (WithLp.norm_snd_le _ _) (hn b))
    rw [hv] at goal
    exact goal
  · rw [hS, Measure.volume_eq_prod, Measure.prod_prod, hball, ENNReal.ofReal_mul (by positivity)]
    gcongr
    exact Formalism.HermitianLatticeCounting.P.s5b7_vol R hR j d hj t ht

theorem norm_det_inv_eq_one {k : ℕ} {m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hm : m ∈ UH (Hb k)) :
    ‖(m⁻¹).det‖ = 1 := by
  have h : mᴴ * Hb k * m = Hb k := hm
  have hH : (Hb k).det ≠ 0 := by
    rw [Hb, det_diagonal]
    refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
    split_ifs <;> simp
  have h2 := congrArg (fun A => ‖Matrix.det A‖) h
  simp only [det_mul, det_conjTranspose, norm_mul, norm_star] at h2
  have hH' : 0 < ‖(Hb k).det‖ := norm_pos_iff.2 hH
  have h3 : ‖m.det‖ ^ 2 = 1 := by
    have : ‖(Hb k).det‖ * ‖m.det‖ ^ 2 = ‖(Hb k).det‖ * 1 := by rw [mul_one]; linarith
    exact mul_left_cancel₀ hH'.ne' this
  have h4 : ‖m.det‖ = 1 := by
    have := norm_nonneg m.det
    nlinarith
  rw [det_nonsing_inv, Ring.inverse_eq_inv', norm_inv, h4, inv_one]

theorem inv_factorial_le (s : ℕ) (hs : 1 ≤ s) : 1 / (s.factorial : ℝ) ≤ (Real.exp 1 / s) ^ s := by
  have h := Real.pow_div_factorial_le_exp (s : ℝ) (Nat.cast_nonneg s) s
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  rw [div_pow, ← Real.exp_nat_mul, mul_one, le_div_iff₀ (by positivity)]
  calc _ = (s : ℝ) ^ s / s.factorial := by ring
    _ ≤ _ := h

theorem vol_gram : ∀ (k j : ℕ), 1 ≤ j → j + 2 ≤ k → ∀ m ∈ UH (Hb k), ∀ P₀ : Submodule ℂ (EuclideanSpace ℂ (Fin (k + 1))), k - 1 ≤ Module.finrank ℂ P₀ → volume {B : Fin j → Fin (k + 1) → ℂ | gramProj P₀ (fun b => m⁻¹ *ᵥ B b) = 0} = 0 ∧ ∀ M y : ℝ, 1 ≤ M → 0 < y → volume {B : Fin j → Fin (k + 1) → ℂ | (∀ b, eucl (m⁻¹ *ᵥ B b) ≤ M) ∧ gramProj P₀ (fun b => m⁻¹ *ᵥ B b) ≤ 2 * y} ≤ ENNReal.ofReal (2 * (Real.pi * M ^ 2) ^ (2 * j) * M ^ (2 * j ^ 2) * Real.pi ^ (j ^ 2) * (Real.pi * Real.exp 1 / ((k - 1 - j : ℕ) : ℝ)) ^ (j * (k - 1 - j)) * (2 * y) ^ (2 * (k - 1 - j))) := by
  intro k j _ hjk m hm P hP
  obtain ⟨d, rfl⟩ : ∃ d, k = d + 1 := ⟨k - 1, by omega⟩
  have hd : d + 1 - 1 = d := by omega
  rw [hd] at hP ⊢
  have key := vol_le d 2 j (by omega) m⁻¹ (norm_det_inv_eq_one hm) P hP
  obtain ⟨s, hs⟩ : ∃ s, d = j + s := ⟨d - j, by omega⟩
  have hs1 : 1 ≤ s := by omega
  have hs2 : d - j = s := by omega
  rw [hs2] at key ⊢
  refine ⟨?_, fun M y hM hy => ?_⟩
  · have hz : ∀ N : ℕ, volume {B : Fin j → Fin (d + 1 + 1) → ℂ | (∀ b, eucl (m⁻¹ *ᵥ B b) ≤ (N : ℝ) + 1) ∧
        gramProj P (fun b => m⁻¹ *ᵥ B b) ≤ 0} = 0 := fun N => by
      have := key ((N : ℝ) + 1) 0 (by positivity) le_rfl
      rw [zero_pow (by omega)] at this
      simpa using this
    refine measure_mono_null ?_ (measure_iUnion_null hz)
    intro B hB
    obtain ⟨N, hN⟩ := exists_nat_ge (∑ b, eucl (m⁻¹ *ᵥ B b))
    refine Set.mem_iUnion.2 ⟨N, fun b => ?_, le_of_eq hB⟩
    have : eucl (m⁻¹ *ᵥ B b) ≤ ∑ b, eucl (m⁻¹ *ᵥ B b) :=
      Finset.single_le_sum (f := fun b => eucl (m⁻¹ *ᵥ B b)) (fun _ _ => Real.sqrt_nonneg _) (Finset.mem_univ b)
    linarith
  · refine le_trans (key M (2 * y) (by positivity) (by positivity)) (ENNReal.ofReal_le_ofReal ?_)
    have hpi := Real.pi_pos
    have h1 : (1 / (s.factorial : ℝ)) ^ j ≤ ((Real.exp 1 / s) ^ s) ^ j :=
      pow_le_pow_left₀ (by positivity) (inv_factorial_le s hs1) j
    have hX : 0 ≤ (Real.pi * M ^ 2) ^ (2 * j) * M ^ (2 * j ^ 2) * Real.pi ^ (j ^ 2) *
        (Real.pi * Real.exp 1 / (s : ℝ)) ^ (j * s) * (2 * y) ^ (2 * s) := by positivity
    calc _ = (Real.pi * M ^ 2) ^ (2 * j) * M ^ (2 * j ^ 2) * Real.pi ^ (j ^ 2) *
          (Real.pi ^ (j * s) * (1 / (s.factorial : ℝ)) ^ j) * (2 * y) ^ (2 * s) := by
          rw [hs, mul_add j j s, pow_add, ← sq j, one_div, inv_pow, div_eq_mul_inv]; ring
      _ ≤ (Real.pi * M ^ 2) ^ (2 * j) * M ^ (2 * j ^ 2) * Real.pi ^ (j ^ 2) *
          (Real.pi ^ (j * s) * ((Real.exp 1 / s) ^ s) ^ j) * (2 * y) ^ (2 * s) := by gcongr
      _ = (Real.pi * M ^ 2) ^ (2 * j) * M ^ (2 * j ^ 2) * Real.pi ^ (j ^ 2) *
          (Real.pi * Real.exp 1 / (s : ℝ)) ^ (j * s) * (2 * y) ^ (2 * s) := by
          rw [← pow_mul, mul_comm s j, ← mul_pow, mul_div_assoc]
      _ ≤ _ := by linarith

end GlobalTheory.Amp.GramVol
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SymmetricKMapEqZeroOfVminusSlices
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SymmetricKMapEqZeroOfVminusSlices
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.Jet

section
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n j : ℕ}

def sliceIns (α' : Fin j → Fin n × Fin n) (m : Arr V n 1) : Arr V n (j + 1) :=
  WithLp.toLp 2 (fun α : Fin (j + 1) → Fin n × Fin n =>
    if Fin.tail α = α' then m (fun _ => α 0) else 0)

theorem slice_sliceIns (α' β' : Fin j → Fin n × Fin n) (m : Arr V n 1) :
    sliceLin V n β' (sliceIns α' m) = if β' = α' then m else 0 := by
  apply indexArray_ext
  intro β
  rw [firstPositionSlice_apply]
  have hβ : (fun _ : Fin 1 => β 0) = β := by
    funext i
    rw [Fin.fin_one_eq_zero i]
  simp only [sliceIns, PiLp.toLp_apply, Fin.tail_cons, Fin.cons_zero]
  split_ifs with h
  · rw [hβ]
  · rfl

theorem sliceIns_mem {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {u : V}
    {α' : Fin j → Fin n × Fin n} (hα : ∀ i, ε (α' i).1 ≠ ε (α' i).2) {m : Arr V n 1}
    (hm : m ∈ arrV0 ε E u 1) : sliceIns α' m ∈ arrV0 ε E u (j + 1) := by
  rw [mem_admissibleArrays]
  intro α
  by_cases ht : Fin.tail α = α'
  · have hv : (sliceIns α' m) α = m (fun _ => α 0) := by simp [sliceIns, ht]
    rw [hv]
    by_cases h0 : ε (α 0).1 ≠ ε (α 0).2
    · have hall : ∀ i, ε (α i).1 ≠ ε (α i).2 := by
        intro i
        cases i using Fin.cases with
        | zero => exact h0
        | succ k =>
          have hk := hα k
          rw [← ht] at hk
          simpa [Fin.tail] using hk
      rw [if_pos hall]
      exact admissibleArrays_apply_mem hm _
    · rw [admissibleArrays_apply_eq_zero hm _ (fun h => h0 (h 0))]
      split_ifs <;> exact Submodule.zero_mem _
  · have hv : (sliceIns α' m) α = 0 := by simp [sliceIns, ht]
    rw [hv]
    split_ifs <;> exact Submodule.zero_mem _

theorem slice_mem_highest_jets {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {u : V}
    {F : Arr V n (j + 1)} (hF : F ∈ arrV0 ε E u (j + 1)) (α' : Fin j → Fin n × Fin n) :
    sliceLin V n α' F ∈ arrV0 ε E u 1 := by
  rw [mem_admissibleArrays]
  intro β
  rw [firstPositionSlice_apply]
  split_ifs with h
  · exact admissibleArrays_apply_mem hF _
  · rw [admissibleArrays_apply_eq_zero hF _ (fun h' => h (fun i => by rw [Fin.fin_one_eq_zero i]; simpa using h' 0))]
    exact Submodule.zero_mem _

theorem slice_eq_zero_of_compact {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {u : V}
    {F : Arr V n (j + 1)} (hF : F ∈ arrV0 ε E u (j + 1)) (α' : Fin j → Fin n × Fin n)
    (hα : ¬ ∀ i, ε (α' i).1 ≠ ε (α' i).2) : sliceLin V n α' F = 0 := by
  apply indexArray_ext
  intro β
  rw [firstPositionSlice_apply, admissibleArrays_apply_eq_zero hF _ (fun h => hα (fun i => by simpa using h i.succ))]
  rfl

theorem permute_mem_highest_jets {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {u : V}
    {F : Arr V n j} (hF : F ∈ arrV0 ε E u j) (s : Equiv.Perm (Fin j)) :
    permArr V n s F ∈ arrV0 ε E u j := by
  rw [mem_admissibleArrays]
  intro α
  rw [permutePositions_apply]
  split_ifs with h
  · exact admissibleArrays_apply_mem hF _
  · rw [admissibleArrays_apply_eq_zero hF _ (fun h' => h (fun i => by simpa using h' (s.symm i)))]
    exact Submodule.zero_mem _

private theorem finiteDimensional_arrV0_of_finiteDimensional_kSpan (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (u : V) (h : FiniteDimensional ℂ (kSpan ε E u)) :
    FiniteDimensional ℂ (arrV0 ε E u j) := by
  let ψ : arrV0 ε E u j →ₗ[ℂ] ((Fin j → Fin n × Fin n) → kSpan ε E u) :=
    LinearMap.pi fun α => LinearMap.codRestrict (kSpan ε E u)
      ((LinearMap.proj α ∘ₗ arrOf V n j) ∘ₗ (arrV0 ε E u j).subtype)
      (fun F => by simpa [arrOf] using admissibleArrays_apply_mem F.2 α)
  refine Module.Finite.of_injective ψ ?_
  intro F G hFG
  apply Subtype.ext
  apply indexArray_ext
  intro α
  have h1 := congrArg Subtype.val (congrFun hFG α)
  simpa [ψ, arrOf] using h1

private theorem permArr_inv_permArr (s : Equiv.Perm (Fin j)) (F : Arr V n j) : permArr V n s⁻¹ (permArr V n s F) = F := by
  apply indexArray_ext
  intro α
  rw [permutePositions_apply, permutePositions_apply]
  simp

end

theorem jet_map_eq_zero : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (g : ℝ) (u : V) (j : ℕ), GlRel E → IsUnitary ε E → KHighest ε E (LamOf ε lam) u → FiniteDimensional ℂ (kSpan ε E u) → (∀ a b : Fin n, a < b → ε a ≠ ε b → g ≤ lam a - lam b) → 2 * (n : ℝ) < g → ∀ T : Arr V n (j + 1) →ₗ[ℂ] V, (∀ F ∈ arrV0 ε E u (j + 1), T F ∈ kSpan ε E u) → (∀ c d, ε c = ε d → ∀ F ∈ arrV0 ε E u (j + 1), T (arrE E (j + 1) c d F) = E c d (T F)) → (∀ F ∈ arrV0 ε E u (j + 1), ∀ s : Equiv.Perm (Fin (j + 1)), T (permArr V n s F) = T F) → (∀ F ∈ arrV0 ε E u (j + 1), (∀ α', sliceLin V n α' F ∈ Vminus ε E (LamOf ε lam) u) → T F = 0) → ∀ F ∈ arrV0 ε E u (j + 1), T F = 0 := by
  intro V _ _ n ε E lam g u j hgl hun hhi hfd hgap hg T hT hE hS hM
  have hsplit := typesSplit V n ε E (LamOf ε lam) u hgl hun hhi hfd
  have hstab := admissibleArrays_invariant ε E u (j + 1)
  let K : Submodule ℂ (Arr V n (j + 1)) := arrV0 ε E u (j + 1) ⊓ LinearMap.ker T
  have memK : ∀ G, G ∈ arrV0 ε E u (j + 1) → T G = 0 → G ∈ K := fun G h1 h2 => ⟨h1, h2⟩

  have key : ∀ f ∈ arrV0 ε E u (j + 1), (∀ k ∈ K, ⟪k, f⟫_ℂ = 0) → f = 0 := by
    intro f hf horth

    have hsym : f ∈ symSub V n (j + 1) := by
      rw [mem_symmetricArrays]
      intro s
      have hGW : permArr V n s f - f ∈ arrV0 ε E u (j + 1) := sub_mem (permute_mem_highest_jets hf s) hf
      have hGT : T (permArr V n s f - f) = 0 := by rw [map_sub, hS f hf s, sub_self]
      have hGK : permArr V n s f - f ∈ K := memK _ hGW hGT
      have hG'K : permArr V n s⁻¹ (permArr V n s f - f) ∈ K :=
        memK _ (permute_mem_highest_jets hGW s⁻¹) (by rw [hS _ hGW s⁻¹, hGT])
      have h1 : ⟪permArr V n s f - f, permArr V n s f⟫_ℂ = 0 := by
        rw [← inner_permutePositions s⁻¹, permArr_inv_permArr]
        exact horth _ hG'K
      have h2 : ⟪permArr V n s f - f, f⟫_ℂ = 0 := horth _ hGK
      have h3 : ⟪permArr V n s f - f, permArr V n s f - f⟫_ℂ = 0 := by
        rw [inner_sub_right, h1, h2, sub_self]
      exact sub_eq_zero.mp (inner_self_eq_zero.mp h3)

    have hplus : ∀ α' : Fin j → Fin n × Fin n, sliceLin V n α' f ∈ Vplus ε E (LamOf ε lam) u := by
      intro α'
      by_cases hα : ∀ i, ε (α' i).1 ≠ ε (α' i).2
      · have hmem : sliceLin V n α' f ∈ Vplus ε E (LamOf ε lam) u ⊔ Vminus ε E (LamOf ε lam) u := by
          rw [hsplit.2]
          exact slice_mem_highest_jets hf α'
        obtain ⟨p, hp, m, hm, hpm⟩ := Submodule.mem_sup.mp hmem
        have hm0 : m ∈ arrV0 ε E u 1 := by
          rw [← hsplit.2]
          exact Submodule.mem_sup_right hm
        have hGW : sliceIns α' m ∈ arrV0 ε E u (j + 1) := sliceIns_mem hα hm0
        have hGT : T (sliceIns α' m) = 0 := by
          apply hM _ hGW
          intro β'
          rw [slice_sliceIns]
          split_ifs
          · exact hm
          · exact Submodule.zero_mem _
        have hin : ⟪sliceIns α' m, f⟫_ℂ = 0 := horth _ (memK _ hGW hGT)
        have hsum : ∑ β' : Fin j → Fin n × Fin n,
            ⟪sliceLin V n β' (sliceIns α' m), sliceLin V n β' f⟫_ℂ = ⟪m, sliceLin V n α' f⟫_ℂ := by
          rw [Finset.sum_eq_single α']
          · rw [slice_sliceIns, if_pos rfl]
          · intro b _ hb
            rw [slice_sliceIns, if_neg hb, inner_zero_left]
          · intro h
            exact absurd (Finset.mem_univ _) h
        rw [inner_eq_sum_firstPositionSlice, hsum, ← hpm, inner_add_right] at hin
        have hmp : ⟪m, p⟫_ℂ = 0 := by
          rw [← inner_conj_symm, hsplit.1 p hp m hm, map_zero]
        rw [hmp, zero_add] at hin
        have hm' : m = 0 := inner_self_eq_zero.mp hin
        rw [← hpm, hm', add_zero]
        exact hp
      · rw [slice_eq_zero_of_compact hf α' hα]
        exact Submodule.zero_mem _
    have hN : f ∈ Formalism.REAL.Nset ε E (LamOf ε lam) u j := by
      unfold Formalism.REAL.Nset
      exact ⟨⟨hf, hsym⟩, (Submodule.mem_iInf _).mpr fun α' => Submodule.mem_comap.mpr (hplus α')⟩

    have hCasW : CasK ε (arrE E (j + 1)) f ∈ arrV0 ε E u (j + 1) := by
      rw [compactCasimir_apply]
      refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
      split_ifs with hab
      · exact hstab a b hab _ (hstab b a hab.symm _ hf)
      · exact Submodule.zero_mem _
    have hCasT : T (CasK ε (arrE E (j + 1)) f) = CasK ε E (T f) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [compactCasimir_apply, compactCasimir_apply, map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      split_ifs with hab
      · rw [hE a b hab _ (hstab b a hab.symm _ hf), hE b a hab.symm _ hf]
      · exact map_zero T
    have hKf : CasK ε E (T f) = ((ckv ε (LamOf ε lam) : ℝ) : ℂ) • T f :=
      kCasSpan V n ε E (LamOf ε lam) u (glRel_kRel ε E hgl) hhi (T f) (hT f hf)
    have hkK : CasK ε (arrE E (j + 1)) f - ((ckv ε (LamOf ε lam) : ℝ) : ℂ) • f ∈ K :=
      memK _ (sub_mem hCasW (Submodule.smul_mem _ _ hf))
        (by rw [map_sub, map_smul, hCasT, hKf, sub_self])
    have hfk : ⟪f, CasK ε (arrE E (j + 1)) f - ((ckv ε (LamOf ε lam) : ℝ) : ℂ) • f⟫_ℂ = 0 := by
      rw [← inner_conj_symm, horth _ hkK, map_zero]
    have hre : (⟪f, CasK ε (arrE E (j + 1)) f⟫_ℂ).re = ckv ε (LamOf ε lam) * ‖f‖ ^ 2 := by
      rw [inner_sub_right, sub_eq_zero] at hfk
      rw [hfk, inner_smul_right, Complex.re_ofReal_mul, re_inner_self_indexArray]

    have hpos := nPos V n ε E lam g u j hgl hun hhi hfd hgap f hN
    rw [hre] at hpos
    have hcoef : 0 < 2 * ((j : ℝ) + 1) * (g - 2 * (n : ℝ)) := by
      have h1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
      have h2 : (0 : ℝ) < g - 2 * (n : ℝ) := by linarith
      positivity
    have h4 : 2 * ((j : ℝ) + 1) * (g - 2 * (n : ℝ)) * ‖f‖ ^ 2 ≤ 0 := by nlinarith
    have h5 : ‖f‖ ^ 2 = 0 := le_antisymm (by nlinarith) (by positivity)
    simpa using h5

  haveI : FiniteDimensional ℂ (arrV0 ε E u (j + 1)) := finiteDimensional_arrV0_of_finiteDimensional_kSpan ε E u hfd
  haveI : FiniteDimensional ℂ K := Submodule.finiteDimensional_of_le inf_le_left
  intro F hF
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.exists_add_mem_mem_orthogonal (K := K) F
  have hzW : z ∈ arrV0 ε E u (j + 1) := by
    have hz' : z = F - y := by rw [hyz]; abel
    rw [hz']
    exact sub_mem hF hy.1
  have hz0 : z = 0 := key z hzW (fun k hk => (Submodule.mem_orthogonal K z).mp hz k hk)
  rw [hyz, hz0, add_zero]
  exact hy.2

end GlobalTheory.Jet
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SymmetricKMapEqZeroOfVminusSlicesStatement
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetric_kMap_eq_zero_of_vminus_slices : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (g : ℝ) (u : V) (j : ℕ), GlRel E → IsUnitary ε E → KHighest ε E (LamOf ε lam) u → FiniteDimensional ℂ (kSpan ε E u) → (∀ a b : Fin n, a < b → ε a ≠ ε b → g ≤ lam a - lam b) → 2 * (n : ℝ) < g → ∀ T : Arr V n (j + 1) →ₗ[ℂ] V, (∀ F ∈ arrV0 ε E u (j + 1), T F ∈ kSpan ε E u) → (∀ c d, ε c = ε d → ∀ F ∈ arrV0 ε E u (j + 1), T (arrE E (j + 1) c d F) = E c d (T F)) → (∀ F ∈ arrV0 ε E u (j + 1), ∀ s : Equiv.Perm (Fin (j + 1)), T (permArr V n s F) = T F) → (∀ F ∈ arrV0 ε E u (j + 1), (∀ α', sliceLin V n α' F ∈ Vminus ε E (LamOf ε lam) u) → T F = 0) → ∀ F ∈ arrV0 ε E u (j + 1), T F = 0 := by
  first | exact @GlobalTheory.Jet.jet_map_eq_zero | exact GlobalTheory.Jet.jet_map_eq_zero | (intros; apply GlobalTheory.Jet.jet_map_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniqueShuffle
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm Formalism.L2.DIV GlobalTheory.FinGL.Bruhat
open scoped Classical

namespace GlobalTheory.GLm.Shuffle

variable {g : ℕ} [Fact g.Prime] {n : ℕ}

theorem pm_eq_mono (σ : Equiv.Perm (Fin n)) : (pm g σ : Mt g n) = mono (σ, fun _ => 1) := by
  have hm : (fun r j : Fin n => if r = σ j then (1 : ZMod g) else 0) = mono (σ, fun _ => (1 : (ZMod g)ˣ)) := by
    ext r j; simp [mono]
  have hu : IsUnit (mono (F := ZMod g) (σ, fun _ => (1 : (ZMod g)ˣ))) := by
    refine IsUnit.of_mul_eq_one (mono (σ.symm, fun _ => (1 : (ZMod g)ˣ))) ?_
    ext r j
    rw [mul_mono]
    simp [mono, Matrix.one_apply]
  unfold pm toG
  rw [hm, dite_eq_left hu]
  rfl

theorem isUniUp_iff (u : Gn g n) : IsUniUp (u : Mt g n) ↔ u ∈ unip (ZMod g) n :=
  ⟨fun h => ⟨fun i j hij => (h i j).1 hij, fun i => (h i i).2 rfl⟩,
    fun h a b => ⟨fun hab => unip_lower h hab, fun e => e ▸ unip_diag h a⟩⟩

theorem inPar_iff (a : ℕ) (p : Gn g n) :
    InPar a (p : Mt g n) ↔ p ∈ blockTri (κ := ZMod g) (fun i : Fin n => if (i : ℕ) < a then 0 else 1 : Fin n → ℕ) := by
  rw [mem_blockTri]
  constructor
  · intro h i j hij
    by_cases hi : (i : ℕ) < a <;> by_cases hj : (j : ℕ) < a <;> simp [hi, hj] at hij
    exact h i j hj (not_lt.1 hi)
  · intro h i j hj hi
    exact h i j (by simp [hj, not_lt.2 hi])

theorem block_of_eq {a : ℕ} {σ σ' : Equiv.Perm (Fin n)} {u u' p p' : Gn g n} (hu : IsUniUp (u : Mt g n))
    (hu' : IsUniUp (u' : Mt g n)) (hp : InPar a (p : Mt g n)) (hp' : InPar a (p' : Mt g n))
    (h : u * pm g σ * p = u' * pm g σ' * p') (r : Fin n) (hr : (σ.symm r : ℕ) < a) : (σ'.symm r : ℕ) < a := by
  have hv : u'⁻¹ * u ∈ unip (ZMod g) n :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ ((isUniUp_iff _).1 hu')) ((isUniUp_iff _).1 hu)
  have hq : InPar a ((p' * p⁻¹ : Gn g n) : Mt g n) :=
    (inPar_iff _ _).2 (Subgroup.mul_mem _ ((inPar_iff _ _).1 hp') (Subgroup.inv_mem _ ((inPar_iff _ _).1 hp)))
  have h1 : (u'⁻¹ * u) * pm g σ = pm g σ' * (p' * p⁻¹) := by
    calc (u'⁻¹ * u) * pm g σ = u'⁻¹ * (u * pm g σ * p) * p⁻¹ := by group
      _ = _ := by rw [h]; group
  have h2 := congrFun (congrFun (congrArg (fun z : Gn g n => (z : Mt g n)) h1) r) (σ.symm r)
  rw [Units.val_mul _ (pm g σ), Units.val_mul (pm g σ'), pm_eq_mono, pm_eq_mono, mul_mono, mono_mul] at h2
  simp only [Equiv.apply_symm_apply, Units.val_one, mul_one, one_mul] at h2
  rw [unip_diag hv] at h2
  by_contra hc
  rw [hq _ _ hr (not_lt.1 hc)] at h2
  exact one_ne_zero h2

noncomputable def key (S : Fin n → Prop) (r : Fin n) : ℕ := if S r then (r : ℕ) else n + r

theorem key_injective (S : Fin n → Prop) : Function.Injective (key S) := by
  intro r s h
  have := r.2; have := s.2
  unfold key at h
  apply Fin.ext
  split_ifs at h <;> omega

theorem key_mono {a : ℕ} {σ : Equiv.Perm (Fin n)} {S : Fin n → Prop} (hS : ∀ r, S r ↔ (σ.symm r : ℕ) < a)
    (hσ : ∀ i j : Fin n, i < j → ((j : ℕ) < a ∨ a ≤ (i : ℕ)) → σ i < σ j) : Monotone (key S ∘ σ) := by
  refine StrictMono.monotone fun i j hij => ?_
  have h1 := hσ i j hij
  have h2 : (i : ℕ) < j := hij
  have := (σ i).2
  simp only [Function.comp, key, hS, Equiv.symm_apply_apply, Fin.lt_def] at h1 ⊢
  split_ifs <;> omega

theorem exists_shuffle {a : ℕ} (ha : a ≤ n) (s : Equiv.Perm (Fin n)) : ∃ σ : Equiv.Perm (Fin n),
    (∀ i j : Fin n, i < j → ((j : ℕ) < a ∨ a ≤ (i : ℕ)) → σ i < σ j) ∧
      ∀ j : Fin n, (s.symm (σ j) : ℕ) < a ↔ (j : ℕ) < a := by
  set S : Fin n → Prop := fun r => (s.symm r : ℕ) < a with hS
  set σ := Tuple.sort (key S) with hσ
  have hm : Monotone (key S ∘ σ) := Tuple.monotone_sort _
  have hlt : ∀ r, key S r < n ↔ S r := by
    intro r
    have := r.2
    unfold key
    split_ifs with h <;> simp [h]
  have hcard : (Finset.univ.filter fun i => (key S ∘ σ) i < n).card = a := by
    have : (Finset.univ.filter fun i : Fin n => (i : ℕ) < a).card = a := by
      rw [Fin.card_filter_val_lt]; omega
    rw [← this]
    refine Finset.card_equiv (σ.trans s.symm) fun i => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp]
    exact hlt _
  have hiff : ∀ j : Fin n, S (σ j) ↔ (j : ℕ) < a := by
    intro j
    rw [← hlt, ← hcard]
    exact (Tuple.lt_card_lt_iff_apply_lt_of_monotone hm).symm
  refine ⟨σ, fun i j hij hb => ?_, hiff⟩
  have h1 : (key S ∘ σ) i < (key S ∘ σ) j :=
    (hm.strictMono_of_injective ((key_injective S).comp σ.injective)) hij
  have h2 : (i : ℕ) < j := hij
  simp only [Function.comp, key, hiff] at h1
  rw [Fin.lt_def]
  split_ifs at h1 <;> omega

theorem existsUnique_shuffle : ∀ (g : ℕ) [Fact g.Prime] (a n : ℕ), a ≤ n → ∀ x : Gn g n, ∃! σ : Equiv.Perm (Fin n), (∀ i j : Fin n, i < j → ((j : ℕ) < a ∨ a ≤ (i : ℕ)) → σ i < σ j) ∧ ∃ u p : Gn g n, IsUniUp (u : Mt g n) ∧ InPar a (p : Mt g n) ∧ x = u * pm g σ * p := by
  intro g _ a n ha x
  obtain ⟨m, u, hu, u', hu', hx⟩ := exists_decomp x
  obtain ⟨σ, hσ, hb⟩ := exists_shuffle ha m.1
  have hp : InPar a (((pm g σ)⁻¹ * u⁻¹ * x : Gn g n) : Mt g n) := by
    intro i j hj hi
    have h1 : (pm g σ : Mt g n) * (((pm g σ)⁻¹ * u⁻¹ * x : Gn g n) : Mt g n) = mono m * (u' : Mt g n) := by
      rw [← Units.val_mul, ← mul_assoc, mul_inv_cancel_left, Units.val_mul, hx, Matrix.mul_assoc,
        Units.inv_mul_cancel_left]
    have h2 := congrFun (congrFun h1 (σ i)) j
    rw [pm_eq_mono, mono_mul, mono_mul] at h2
    simp only [Equiv.symm_apply_apply, Units.val_one, one_mul] at h2
    have h3 : j < m.1.symm (σ i) := by
      have := (hb i).not.2 (not_lt.2 hi)
      rw [Fin.lt_def]; omega
    rw [h2, unip_lower hu' h3, mul_zero]
  have hu1 := (isUniUp_iff u).2 hu
  have hx1 : x = u * pm g σ * ((pm g σ)⁻¹ * u⁻¹ * x) := by group
  refine ⟨σ, ⟨hσ, u, _, hu1, hp, hx1⟩, ?_⟩
  rintro τ ⟨hτ, v, q, hv, hq, hx2⟩
  have h1 : Monotone (key (fun r => (σ.symm r : ℕ) < a) ∘ σ) := key_mono (fun _ => Iff.rfl) hσ
  have h2 : Monotone (key (fun r => (σ.symm r : ℕ) < a) ∘ τ) := key_mono (fun r =>
    ⟨block_of_eq hu1 hv hp hq (hx1.symm.trans hx2) r, block_of_eq hv hu1 hq hp (hx2.symm.trans hx1) r⟩) hτ
  exact Equiv.ext fun i => key_injective _ (congrFun (Tuple.unique_monotone h2 h1) i)

end GlobalTheory.GLm.Shuffle
end
