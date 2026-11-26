module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.KkCpt
public import Development.AutomorphicArithmetic.WhittakerHecke.ZetaIntegralEqLseriesMulGammaMulEvalOfMemLevel
public import Development.AutomorphicArithmetic.WhittakerHecke.TwistedZetaIntegralAtCompactEqAtRotation
public import Development.AutomorphicArithmetic.WhittakerHecke.HasSumTwistedZetaIntegralDirichletSeries
public import Development.AutomorphicArithmetic.WhittakerHecke.MeasurableAndBoundedTwistedZetaIntegralRotation
public import Development.AutomorphicArithmetic.WhittakerHecke.ExistsWhittakerHeckeEigenvaluesAndCoeffEqConvolu

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.ZetaIntegralEqZeroOfMemMaximalCompactNotMemLevel
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem loc_dv {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (w : Valuation K Γ) {c d z n : K}
    (hc : w c ≤ 1) (hd : w d ≤ 1) (hn : w n ≤ 1) (h0 : w (z * c) ≤ w n) (h1 : w (z * d - 1) ≤ w n) : w c ≤ w n := by
  rcases lt_or_eq_of_le hn with hlt | heq
  · have h2 : w (z * d - 1) < w 1 := by rw [map_one]; exact h1.trans_lt hlt
    have h3 : w (z * d) = 1 := by
      have e : z * d = (z * d - 1) + 1 := by ring
      rw [e, Valuation.map_add_eq_of_lt_right w h2, map_one]
    have h4 : 1 ≤ w z := by
      rw [map_mul] at h3
      calc (1 : Γ) = w z * w d := h3.symm
        _ ≤ w z * 1 := mul_le_mul' le_rfl hd
        _ = w z := mul_one _
    calc w c = 1 * w c := (one_mul _).symm
      _ ≤ w z * w c := mul_le_mul' h4 le_rfl
      _ = w (z * c) := (map_mul _ _ _).symm
      _ ≤ w n := h0
  · rw [heq]
    exact hc

private theorem nat_le_one (v : H.P ℚ) (N : ℕ) : Valued.v (N : H.Kv v) ≤ 1 := by
  have h : (N : H.Kv v) ∈ v.adicCompletionIntegers ℚ := natCast_mem _ N
  exact h

theorem UpperTheory.zeta_integral_eq_zero_of_mem_maximal_compact_not_mem_level :
    ∀ (N : ℕ), 0 < N → ∀ (p : MvPolynomial (Fin 2) ℂ) (s : ℂ), ∀ k ∈ KK ℚ, k ∉ SS N → Zr N p s k = 0 := by
  intro N _ p s k hk hkS
  have hz : ∀ z : IdeleGroup ℚ, (PhiN N p fun j => ((z : (A ℚ)ˣ) : A ℚ) * row k j) = 0 := by
    intro z
    unfold PhiN
    rw [if_neg]
    intro h
    apply hkS
    intro v
    obtain ⟨h0, h1⟩ := h v
    have hint : ∀ i j, Valued.v (H.cp v (k i j)) ≤ 1 := fun i j => hk.2 v i j
    have e0 : H.cp v (((z : (A ℚ)ˣ) : A ℚ) * row k 0) = H.cp v ((z : (A ℚ)ˣ) : A ℚ) * H.cp v (k 1 0) := map_mul _ _ _
    have e1 : H.cp v (((z : (A ℚ)ˣ) : A ℚ) * row k 1 - 1) = H.cp v ((z : (A ℚ)ˣ) : A ℚ) * H.cp v (k 1 1) - 1 := by
      rw [map_sub, map_one]
      exact congrArg (· - 1) (map_mul _ _ _)
    have h0' : Valued.v (H.cp v (((z : (A ℚ)ˣ) : A ℚ) * row k 0)) ≤ Valued.v (N : H.Kv v) := h0
    have h1' : Valued.v (H.cp v (((z : (A ℚ)ˣ) : A ℚ) * row k 1 - 1)) ≤ Valued.v (N : H.Kv v) := h1
    rw [e0] at h0'
    rw [e1] at h1'
    exact loc_dv Valued.v (hint 1 0) (hint 1 1) (nat_le_one v N) h0' h1'
  simp only [Zr, hz, zero_mul, MeasureTheory.integral_zero]
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.IntegralMaxCompactEqCircleAverage
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private noncomputable def Mr (t : ℝ) : Matrix (Fin 2) (Fin 2) (TR.Rinf ℚ) :=
  !![fun _ => Real.cos t, fun _ => -Real.sin t; fun _ => Real.sin t, fun _ => Real.cos t]

private theorem rot_inf (t : ℝ) (i j : Fin 2) :
    TR.pInf ℚ ((UpperTheory.ConvolutionTheory.RankTwoDescent.rot t).val i j) = Mr t i j := by
  unfold UpperTheory.ConvolutionTheory.RankTwoDescent.rot
  exact congrArg (fun g : GL (Fin 2) (TR.Rinf ℚ) => g.val i j) (TR.pInf_infGL _)

private theorem rot_fin (t : ℝ) (i j : Fin 2) :
    pFin ℚ ((UpperTheory.ConvolutionTheory.RankTwoDescent.rot t).val i j) = ((1 : Matrix (Fin 2) (Fin 2) (Af ℚ)) i j) := by
  unfold UpperTheory.ConvolutionTheory.RankTwoDescent.rot
  exact congrArg (fun g : GL (Fin 2) (Af ℚ) => g.val i j) (TR.pFin_infGL _)

private theorem cont_re : Continuous UpperTheory.ConvolutionTheory.RankTwoDescent.re := by
  have h : Continuous (TR.infEq ℚ).symm :=
    continuous_pi fun w =>
      (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
        (continuous_apply w)
  exact (continuous_apply _).comp (h.comp continuous_fst)

private noncomputable def reH : A ℚ →+* ℝ :=
  (Pi.evalRingHom (fun _ : InfinitePlace ℚ => ℝ) Rat.infinitePlace).comp (TR.pInf ℚ)

private theorem re_eq (x : A ℚ) : UpperTheory.ConvolutionTheory.RankTwoDescent.re x = reH x := rfl

private theorem cont_entry (i j : Fin 2) : Continuous fun k : G1 ℚ => k i j :=
  Matrix.SpecialLinearGroup.isClosedEmbedding_val.continuous.matrix_elem i j

private noncomputable def Rr (t : ℝ) : G1 ℚ := ⟨(UpperTheory.ConvolutionTheory.RankTwoDescent.rot t).val, by
  rw [Matrix.det_fin_two]
  apply TR.ad_ext
  · simp only [map_sub, map_mul, map_one, rot_inf]
    funext w
    simp [Mr]
    nlinarith [Real.sin_sq_add_cos_sq t]
  · simp only [map_sub, map_mul, map_one, rot_fin]
    simp⟩

private theorem Rr_inf (t : ℝ) (i j : Fin 2) : TR.pInf ℚ ((Rr t) i j) = Mr t i j := rot_inf t i j
private theorem Rr_fin (t : ℝ) (i j : Fin 2) :
    pFin ℚ ((Rr t) i j) = ((1 : Matrix (Fin 2) (Fin 2) (Af ℚ)) i j) := rot_fin t i j

private theorem inf_ext {x y : A ℚ} (h : TR.pInf ℚ x = TR.pInf ℚ y) : x.1 = y.1 :=
  (TR.infEq ℚ).symm.injective h

private theorem Rr_mem (t : ℝ) : Rr t ∈ KK ℚ := by
  refine ⟨?_, ?_⟩
  · intro i j
    apply inf_ext
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, map_add (f := _), map_mul, Rr_inf]
    fin_cases i <;> fin_cases j <;> funext w <;> simp [Mr] <;> nlinarith [Real.sin_sq_add_cos_sq t]
  · intro v i j
    have h : ((Rr t) i j).2 = ((1 : Matrix (Fin 2) (Fin 2) (Af ℚ)) i j) := Rr_fin t i j
    rw [h, Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

private theorem rotation_entry_sin (t : ℝ) : UpperTheory.ConvolutionTheory.RankTwoDescent.re ((Rr t) 1 0) = Real.sin t := by
  have := congrFun (Rr_inf t 1 0) Rat.infinitePlace
  change TR.pInf ℚ _ _ = _
  simpa [Mr] using this
private theorem rotation_entry_cos (t : ℝ) : UpperTheory.ConvolutionTheory.RankTwoDescent.re ((Rr t) 1 1) = Real.cos t := by
  have := congrFun (Rr_inf t 1 1) Rat.infinitePlace
  change TR.pInf ℚ _ _ = _
  simpa [Mr] using this

private theorem Rr_cp (t : ℝ) (v : H.P ℚ) (i j : Fin 2) :
    H.cp v ((Rr t) i j) = ((1 : Matrix (Fin 2) (Fin 2) (H.Kv v)) i j) := by
  change pLoc ℚ v (pFin ℚ ((Rr t) i j)) = _
  rw [Rr_fin, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · exact map_one _
  · exact map_zero _

private theorem mul_mem_SS (N : ℕ) (u : ℝ) (k : G1 ℚ) : Rr u * k ∈ SS N ↔ k ∈ SS N := by
  have h : ∀ v, H.cp v ((Rr u * k) 1 0) = H.cp v (k 1 0) := by
    intro v
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, map_add (f := _), map_mul, Rr_cp]
  simp only [SS, Dv, Set.mem_setOf_eq, h]

private theorem Rr_SS (N : ℕ) (t : ℝ) : Rr t ∈ SS N := by
  intro v
  simp [Dv, Rr_cp]

private theorem SS_closed (N : ℕ) (hN : 0 < N) : IsClosed (SS N) := by
  have : SS N = ⋂ v, {k : G1 ℚ | Dv N v (k 1 0)} := by
    ext k; simp [SS]
  rw [this]
  refine isClosed_iInter fun v => ?_
  have hc : ((N : H.Kv v)) ≠ 0 := by exact_mod_cast hN.ne'
  have hcp : Continuous (H.cp v) := by
    have h1 : Continuous (pLoc ℚ v) := RestrictedProduct.continuous_eval (R := fun v : H.P ℚ => v.adicCompletion ℚ) v
    exact h1.comp continuous_snd
  have hset : {k : G1 ℚ | Dv N v (k 1 0)} =
      (fun k : G1 ℚ => H.cp v (k 1 0) * (N : H.Kv v)⁻¹) ⁻¹' (Valued.integer (H.Kv v) : Set (H.Kv v)) := by
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe, Dv]
    change _ ↔ Valued.v (H.cp v (k 1 0) * (N : H.Kv v)⁻¹) ≤ 1
    rw [map_mul, map_inv₀, ← div_eq_mul_inv, div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hc))]
  rw [hset]
  exact (Valued.isClosed_integer (H.Kv v)).preimage ((hcp.comp (cont_entry 1 0)).mul continuous_const)

private theorem kk_rel {k : G1 ℚ} (hk : k ∈ KK ℚ) :
    UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 0 0) = UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 1 1) ∧ UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 0 1) = - UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 1 0) ∧
      UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 1 0) ^ 2 + UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 1 1) ^ 2 = 1 := by
  have key : ∀ i j, reH ((k.1 * k.1ᵀ) i j) = reH ((1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j) := by
    intro i j
    change (TR.infEq ℚ).symm ((k.1 * k.1ᵀ) i j).1 _ = (TR.infEq ℚ).symm ((1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j).1 _
    rw [hk.1 i j]
  have h00 := key 0 0
  have h01 := key 0 1
  have h11 := key 1 1
  have hd : reH (k.1 0 0 * k.1 1 1 - k.1 0 1 * k.1 1 0) = 1 := by
    rw [← Matrix.det_fin_two, k.det_coe, map_one]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, map_add (f := _), map_mul, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide), map_one, map_zero] at h00 h01 h11
  simp only [map_sub, map_mul] at hd
  simp only [re_eq]
  generalize reH (k.1 0 0) = a at *
  generalize reH (k.1 0 1) = b at *
  generalize reH (k.1 1 0) = c at *
  generalize reH (k.1 1 1) = d at *
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (-a) * h11 + c * h01 + d * hd
  · linear_combination (-b) * h11 + d * h01 - c * hd
  · nlinarith

private noncomputable def th (k : G1 ℚ) : ℝ :=
  Complex.arg ⟨UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 1 1), UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 1 0)⟩

private theorem th_meas : Measurable th := by
  have h : Continuous fun k : G1 ℚ => (⟨UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 1 1), UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 1 0)⟩ : ℂ) := by
    have h1 := cont_re.comp (cont_entry 1 1)
    have h0 := cont_re.comp (cont_entry 1 0)
    have : (fun k : G1 ℚ => (⟨UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 1 1), UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 1 0)⟩ : ℂ)) =
        fun k => Complex.equivRealProdCLM.symm (UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 1 1), UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 1 0)) := by
      funext k; apply Complex.ext <;> simp
    rw [this]
    exact Complex.equivRealProdCLM.symm.continuous.comp (h1.prodMk h0)
  exact Complex.measurable_arg.comp h.measurable

private theorem th_sin_cos {k : G1 ℚ} (hk : k ∈ KK ℚ) :
    UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 1 0) = Real.sin (th k) ∧ UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 1 1) = Real.cos (th k) := by
  obtain ⟨-, -, h⟩ := kk_rel hk
  set z : ℂ := ⟨UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 1 1), UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 1 0)⟩ with hz
  have hn : ‖z‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_apply, Real.sqrt_eq_one]
    simp only [hz]
    nlinarith
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0] at hn
    simp at hn
  constructor
  · have := Complex.sin_arg z
    rw [hn, div_one] at this
    exact this.symm
  · have := Complex.cos_arg hz0
    rw [hn, div_one] at this
    exact this.symm

private theorem mul_re {u : ℝ} {k : G1 ℚ} (hk : k ∈ KK ℚ) :
    UpperTheory.ConvolutionTheory.RankTwoDescent.re ((Rr u * k) 1 0) = Real.sin (th k + u) ∧
      UpperTheory.ConvolutionTheory.RankTwoDescent.re ((Rr u * k) 1 1) = Real.cos (th k + u) := by
  obtain ⟨h0, h1, -⟩ := kk_rel hk
  obtain ⟨hs, hc⟩ := th_sin_cos hk
  have e0 : UpperTheory.ConvolutionTheory.RankTwoDescent.re ((Rr u * k) 1 0) = UpperTheory.ConvolutionTheory.RankTwoDescent.re ((Rr u) 1 0) * UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 0 0) +
      UpperTheory.ConvolutionTheory.RankTwoDescent.re ((Rr u) 1 1) * UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 1 0) := by
    simp only [re_eq, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, map_add (f := _), map_mul]
  have e1 : UpperTheory.ConvolutionTheory.RankTwoDescent.re ((Rr u * k) 1 1) = UpperTheory.ConvolutionTheory.RankTwoDescent.re ((Rr u) 1 0) * UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 0 1) +
      UpperTheory.ConvolutionTheory.RankTwoDescent.re ((Rr u) 1 1) * UpperTheory.ConvolutionTheory.RankTwoDescent.re (k 1 1) := by
    simp only [re_eq, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, map_add (f := _), map_mul]
  rw [e0, e1, rotation_entry_sin, rotation_entry_cos, h0, h1, hs, hc, Real.sin_add, Real.cos_add]
  constructor <;> ring

private theorem avg {X : Type} [MeasurableSpace X] (κ : Measure X) [IsProbabilityMeasure κ] (S : Set X)
    (hS : MeasurableSet S) (θ : X → ℝ) (hθ : Measurable θ) (H' : ℝ → ℂ) (hH : Measurable H') (C : ℝ)
    (hC : ∀ t, ‖H' t‖ ≤ C) (hper : Function.Periodic H' (2 * Real.pi)) (I : ℂ)
    (hinv : ∀ u : ℝ, I = ∫ k, S.indicator (fun k => H' (θ k + u)) k ∂κ) :
    (2 * Real.pi : ℝ) • I = κ.real S • ∫ t in (0 : ℝ)..2 * Real.pi, H' t := by
  let Fu : ℝ → X → ℂ := fun u => S.indicator fun k => H' (θ k + u)
  have hFm : Measurable (Function.uncurry Fu) := by
    have h2 : Measurable fun p : ℝ × X => H' (θ p.2 + p.1) :=
      hH.comp ((hθ.comp measurable_snd).add measurable_fst)
    have h3 : Function.uncurry Fu = (Set.univ ×ˢ S).indicator fun p : ℝ × X => H' (θ p.2 + p.1) := by
      funext p
      by_cases hp : p.2 ∈ S <;> simp [Fu, Function.uncurry, Set.indicator, hp]
    rw [h3]
    exact h2.indicator (MeasurableSet.univ.prod hS)
  set J : ℂ := ∫ t in (0 : ℝ)..2 * Real.pi, H' t with hJ
  have hbound : ∀ p : ℝ × X, ‖Function.uncurry Fu p‖ ≤ C := by
    intro p
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
    by_cases hp : p.2 ∈ S
    · simpa [Fu, Function.uncurry, hp] using hC _
    · simpa [Fu, Function.uncurry, hp] using hC0
  have hint : Integrable (Function.uncurry Fu) ((volume.restrict (Set.Ioc 0 (2 * Real.pi))).prod κ) :=
    Integrable.of_bound hFm.aestronglyMeasurable C (Eventually.of_forall hbound)
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hinner : ∀ k, ∫ u in Set.Ioc 0 (2 * Real.pi), Fu u k = S.indicator (fun _ => J) k := by
    intro k
    by_cases hs : k ∈ S
    · simp only [Fu, Set.indicator_of_mem hs]
      rw [← intervalIntegral.integral_of_le hpi, intervalIntegral.integral_comp_add_left (fun t => H' t) (θ k)]
      have := hper.intervalIntegral_add_eq (θ k) 0
      rw [zero_add] at this
      rw [add_zero]
      exact this
    · simp [Fu, hs]
  calc (2 * Real.pi : ℝ) • I
      = ∫ _u in Set.Ioc 0 (2 * Real.pi), I := by
        simp [hpi]
    _ = ∫ u in Set.Ioc 0 (2 * Real.pi), ∫ k, Fu u k ∂κ := by
        refine integral_congr_ae (Eventually.of_forall fun u => hinv u)
    _ = ∫ k, ∫ u in Set.Ioc 0 (2 * Real.pi), Fu u k ∂volume ∂κ := integral_integral_swap hint
    _ = ∫ k, S.indicator (fun _ => J) k ∂κ := by simp_rw [hinner]
    _ = κ.real S • J := integral_indicator_const _ hS

theorem UpperTheory.integral_maxCompact_eq_circle_average :
    ∀ (M : Meas ℚ) (N : ℕ), 0 < N → ∀ (A' : G1 ℚ → ℂ) (H' : ℝ → ℂ), Measurable H' → (∃ C : ℝ, ∀ t, ‖H' t‖ ≤ C) →
        (∀ k ∈ KK ℚ, k ∉ SS N → A' k = 0) →
        (∀ k ∈ KK ℚ, k ∈ SS N → ∀ t : ℝ, re (k 1 0) = Real.sin t → re (k 1 1) = Real.cos t → A' k = H' t) →
        ∫ k, A' k ∂M.κ = ((cK M N / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (0 : ℝ)..2 * Real.pi, H' t := by
  intro M N hN A' H' hH ⟨C, hC⟩ h0 h1
  haveI := M.prob
  have hS : MeasurableSet (SS N) := (SS_closed N hN).measurableSet
  have hper : Function.Periodic H' (2 * Real.pi) := fun t => by
    have e1 := h1 (Rr t) (Rr_mem t) (Rr_SS N t) t (rotation_entry_sin t) (rotation_entry_cos t)
    have e2 := h1 (Rr t) (Rr_mem t) (Rr_SS N t) (t + 2 * Real.pi)
      (by rw [rotation_entry_sin, Real.sin_add_two_pi]) (by rw [rotation_entry_cos, Real.cos_add_two_pi])
    exact e2.symm.trans e1
  have hKK : ∀ᵐ k ∂M.κ, k ∈ KK ℚ := by
    rw [ae_iff]
    exact M.supp
  have hFm : ∀ u : ℝ, Measurable ((SS N).indicator fun k => H' (th k + u)) := fun u =>
    (hH.comp (th_meas.add_const u)).indicator hS
  have key : ∀ u : ℝ, ∀ k ∈ KK ℚ, A' (Rr u * k) = (SS N).indicator (fun k => H' (th k + u)) k := by
    intro u k hk
    have hk' : Rr u * k ∈ KK ℚ := by
      obtain ⟨hKs, -⟩ := UpperTheory.ConvolutionTheory.R2.M.kkCpt ℚ
      have a1 := Rr_mem u
      rw [hKs] at a1 hk ⊢
      exact (UpperTheory.ConvolutionTheory.R2.M.Ks ℚ).mul_mem a1 hk
    by_cases hs : k ∈ SS N
    · rw [h1 _ hk' ((mul_mem_SS N u k).2 hs) (th k + u) (mul_re hk).1 (mul_re hk).2, Set.indicator_of_mem hs]
    · rw [h0 _ hk' (fun h => hs ((mul_mem_SS N u k).1 h)), Set.indicator_of_notMem hs]
  have hA0 : A' =ᵐ[M.κ] (SS N).indicator fun k => H' (th k + 0) := by
    refine hKK.mono fun k hk => ?_
    by_cases hs : k ∈ SS N
    · rw [h1 k hk hs (th k) (th_sin_cos hk).1 (th_sin_cos hk).2, Set.indicator_of_mem hs, add_zero]
    · rw [h0 k hk hs, Set.indicator_of_notMem hs]
  have hAs : AEStronglyMeasurable A' M.κ := (hFm 0).aestronglyMeasurable.congr hA0.symm
  have hinv : ∀ u : ℝ, ∫ k, A' k ∂M.κ = ∫ k, (SS N).indicator (fun k => H' (th k + u)) k ∂M.κ := by
    intro u
    have hm : Measurable (fun x : G1 ℚ => Rr u * x) := (continuous_const.mul continuous_id).measurable
    calc ∫ k, A' k ∂M.κ = ∫ k, A' k ∂(M.κ.map (Rr u * ·)) := by rw [M.κ_left _ (Rr_mem u)]
      _ = ∫ k, A' (Rr u * k) ∂M.κ :=
        integral_map hm.aemeasurable (by rw [M.κ_left _ (Rr_mem u)]; exact hAs)
      _ = _ := integral_congr_ae (hKK.mono fun k hk => key u k hk)
  have hmain := avg M.κ (SS N) hS th th_meas H' hH C hC hper _ hinv
  have hc : M.κ.real (SS N) = cK M N := by
    simp only [cK, Measure.real]
    rw [measure_inter_conull M.supp]
  rw [hc] at hmain
  have hpi0 : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hpc : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpi0
  simp only [Complex.real_smul] at hmain
  rw [Complex.ofReal_div, div_mul_eq_mul_div, eq_div_iff hpc, mul_comm]
  exact hmain
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.LseriesTwistedCoeffEqTsumCoprimeOfSummable
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.lseries_twisted_coeff_eq_tsum_coprime_of_summable :
    ∀ (N : ℕ) (χ : HChar ℚ) (μ : ℕ → ℂ) (s : ℂ),
        Summable (fun n : {n : ℕ // 0 < n ∧ n.Coprime N} => μ n * ((χ.1 (pin n) : ℂˣ) : ℂ) * (n : ℂ) ^ (1 - s)) →
        LSeriesSummable (bN N χ μ) s ∧
          LSeries (bN N χ μ) s = ∑' n : {n : ℕ // 0 < n ∧ n.Coprime N}, μ n * ((χ.1 (pin n) : ℂˣ) : ℂ) * (n : ℂ) ^ (1 - s) := by
  intro N χ μ s hS
  have hterm : ∀ n : {n : ℕ // 0 < n ∧ n.Coprime N}, LSeries.term (bN N χ μ) s (n : ℕ) =
      μ n * ((χ.1 (pin n) : ℂˣ) : ℂ) * (n : ℂ) ^ (1 - s) := by
    rintro ⟨n, hn, hc⟩
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [LSeries.term_of_ne_zero hn.ne']
    simp only [bN, if_pos hc]
    rw [Complex.cpow_sub _ _ hn0, Complex.cpow_one]
    ring
  have hzero : ∀ x ∉ Set.range (Subtype.val : {n : ℕ // 0 < n ∧ n.Coprime N} → ℕ),
      LSeries.term (bN N χ μ) s x = 0 := by
    intro x hx
    by_cases h0 : x = 0
    · rw [h0, LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero h0]
      have hc : ¬ x.Coprime N := fun hc => hx ⟨⟨x, Nat.pos_of_ne_zero h0, hc⟩, rfl⟩
      simp only [bN, if_neg hc, zero_div]
  have heq : (LSeries.term (bN N χ μ) s) ∘ (Subtype.val : {n : ℕ // 0 < n ∧ n.Coprime N} → ℕ) =
      fun n : {n : ℕ // 0 < n ∧ n.Coprime N} => μ n * ((χ.1 (pin n) : ℂˣ) : ℂ) * (n : ℂ) ^ (1 - s) :=
    funext hterm
  refine ⟨(Subtype.val_injective.summable_iff hzero).1 (heq ▸ hS), ?_⟩
  have hsupp : Function.support (LSeries.term (bN N χ μ) s) ⊆
      Set.range (Subtype.val : {n : ℕ // 0 < n ∧ n.Coprime N} → ℕ) := by
    intro x hx
    by_contra h
    exact hx (hzero x h)
  rw [LSeries, ← Subtype.val_injective.tsum_eq hsupp]
  exact tsum_congr hterm
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.LseriesSummableSqCoeffOfFourLtRe
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.lseries_summable_sq_coeff_of_four_lt_re :
    ∀ (N : ℕ) (s : ℂ), 4 < s.re → LSeriesSummable (sqN N) s := by
  intro N s hs
  refine LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => ?_) (by linarith)
  unfold sqN
  split_ifs <;> simp
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.CongruenceSubgroupVolumePos
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem kappa_ne_zero (M : Meas ℚ)
    {U : Set (G1 ℚ)} (hU : IsOpen U) {k : G1 ℚ} (hk : k ∈ KK ℚ) (hkU : k ∈ U) : M.κ U ≠ 0 := by
  intro h0
  obtain ⟨hKs, hC⟩ := UpperTheory.ConvolutionTheory.R2.M.kkCpt ℚ
  have hmem : ∀ x ∈ KK ℚ, ∀ y ∈ KK ℚ, x * y⁻¹ ∈ KK ℚ := by
    intro x hx y hy
    rw [hKs] at hx hy ⊢
    exact (UpperTheory.ConvolutionTheory.R2.M.Ks ℚ).mul_mem hx ((UpperTheory.ConvolutionTheory.R2.M.Ks ℚ).inv_mem hy)
  have hnull : ∀ c ∈ KK ℚ, M.κ ((fun x => c * x) ⁻¹' U) = 0 := by
    intro c hc
    have hm : Measurable (fun x : G1 ℚ => c * x) := (continuous_const.mul continuous_id).measurable
    rw [← Measure.map_apply hm hU.measurableSet, M.κ_left c hc]
    exact h0
  obtain ⟨t, ht, hcov⟩ := hC.elim_nhds_subcover (fun x => (fun y => (k * x⁻¹) * y) ⁻¹' U) (by
    intro x hx
    refine ((continuous_const.mul continuous_id).isOpen_preimage _ hU).mem_nhds ?_
    simpa using hkU)
  have hK0 : M.κ (KK ℚ) = 0 := by
    refine measure_mono_null hcov ?_
    exact (measure_biUnion_null_iff t.countable_toSet).2 fun x hx => hnull _ (hmem k hk x (ht x hx))
  haveI := M.prob
  have hle : M.κ Set.univ ≤ M.κ (KK ℚ) + M.κ (KK ℚ)ᶜ := by
    rw [← Set.union_compl_self (KK ℚ)]
    exact measure_union_le _ _
  rw [hK0, M.supp, measure_univ] at hle
  simp at hle

private theorem cp_cont (v : H.P ℚ) : Continuous (H.cp v) := by
  have h1 : Continuous (pLoc ℚ v) :=
    RestrictedProduct.continuous_eval (R := fun v : H.P ℚ => v.adicCompletion ℚ) v
  have h2 : Continuous (pFin ℚ) := continuous_snd
  exact h1.comp h2

private theorem isOpen_dv {N : ℕ} (hN : 0 < N) (v : H.P ℚ) :
    IsOpen {k : G1 ℚ | Dv N v (k 1 0)} := by
  have hN0 : (N : H.Kv v) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hv0 : Valued.v (N : H.Kv v) ≠ 0 := (Valuation.ne_zero_iff _).2 hN0
  have hO : IsOpen ((v.adicCompletionIntegers ℚ : ValuationSubring (H.Kv v)) : Set (H.Kv v)) :=
    Valued.isOpen_valuationSubring _
  have hc : Continuous fun k : G1 ℚ => H.cp v (k 1 0) * (N : H.Kv v)⁻¹ := by
    have hk : Continuous fun k : G1 ℚ => (k.1 : Matrix (Fin 2) (Fin 2) (A ℚ)) 1 0 :=
      (Matrix.SpecialLinearGroup.isClosedEmbedding_val.continuous).matrix_elem 1 0
    exact ((cp_cont v).comp hk).mul continuous_const
  have : {k : G1 ℚ | Dv N v (k 1 0)} =
      (fun k : G1 ℚ => H.cp v (k 1 0) * (N : H.Kv v)⁻¹) ⁻¹' ((v.adicCompletionIntegers ℚ : ValuationSubring (H.Kv v)) : Set (H.Kv v)) := by
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe, Dv]
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀]
    rw [← div_eq_mul_inv]
    exact (div_le_one₀ (zero_lt_iff.2 hv0)).symm
  rw [this]
  exact hO.preimage hc

private theorem val_nat {K : Type} [Field K] [NumberField K] (v : H.P K) (n : ℕ) :
    Valued.v (n : H.Kv v) = v.valuation K (n : K) := by
  rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (n : K)]
  congr 1
  exact (map_natCast (algebraMap K (H.Kv v)) n).symm

private theorem dv_of_int {N : ℕ} (hN : 0 < N) (v : H.P ℚ)
    (hv : v ∉ HeightOneSpectrum.Support (𝓞 ℚ) ((N : ℚ)⁻¹)) {x : A ℚ}
    (hx : Valued.v (H.cp v x) ≤ 1) : Dv N v x := by
  have h1 : ¬ 1 < v.valuation ℚ ((N : ℚ)⁻¹) := hv
  have hN0 : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have h2 : (1 : _) ≤ v.valuation ℚ (N : ℚ) := by
    rw [map_inv₀] at h1
    have h3 := not_lt.1 h1
    have hp : 0 < v.valuation ℚ (N : ℚ) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hN0)
    exact (inv_le_one₀ hp).1 h3
  have h4 : Valued.v (N : H.Kv v) = v.valuation ℚ (N : ℚ) := val_nat v N
  refine hx.trans ?_
  rw [h4]
  exact h2

theorem UpperTheory.congruenceSubgroup_volume_pos :
    ∀ (M : Meas ℚ) (N : ℕ), 0 < N → 0 < cK M N := by
  intro M N hN
  haveI := M.prob
  have hfin := HeightOneSpectrum.Support.finite (𝓞 ℚ) ((N : ℚ)⁻¹)
  set T := HeightOneSpectrum.Support (𝓞 ℚ) ((N : ℚ)⁻¹) with hT
  set U : Set (G1 ℚ) := ⋂ v ∈ T, {k : G1 ℚ | Dv N v (k 1 0)} with hU
  have hUo : IsOpen U := hfin.isOpen_biInter fun v _ => isOpen_dv hN v
  have h1K : (1 : G1 ℚ) ∈ KK ℚ := by
    rw [(UpperTheory.ConvolutionTheory.R2.M.kkCpt ℚ).1]
    exact (UpperTheory.ConvolutionTheory.R2.M.Ks ℚ).one_mem
  have h1U : (1 : G1 ℚ) ∈ U := by
    refine Set.mem_iInter₂.2 fun v _ => ?_
    simp [Dv]
  have hne := kappa_ne_zero M hUo h1K h1U
  refine ENNReal.toReal_pos (fun h0 => hne ?_) (measure_ne_top _ _)
  refine measure_mono_null (t := (SS N ∩ KK ℚ) ∪ (KK ℚ)ᶜ) ?_ (measure_union_null h0 M.supp)
  intro k hk
  by_cases hkK : k ∈ KK ℚ
  · refine Or.inl ⟨fun v => ?_, hkK⟩
    by_cases hv : v ∈ T
    · exact Set.mem_iInter₂.1 hk v hv
    · refine dv_of_int hN v hv ?_
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hkK.2 v 1 0)
  · exact Or.inr hkK
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.FiniteIdeleCongruenceVolumePos
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private lemma eq_one_of_mul'' {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a b : Γ}
    (ha : a ≤ 1) (hb : b ≤ 1) (h : a * b = 1) : a = 1 := by
  refine le_antisymm ha ?_
  have := mul_le_mul' (le_refl a) hb
  rwa [h, mul_one] at this

private noncomputable def ef (x : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (A ℚ)ˣ := (IdeleGroup.prodEquiv ℚ).symm (1, x)

private lemma ef_fst (x : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ((ef x : (A ℚ)ˣ) : A ℚ).1 = 1 := rfl

private lemma inv_mul_at (x : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (v : H.P ℚ) :
    Valued.v (((x⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v) *
      Valued.v ((x : FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1 := by
  rw [← map_mul]
  have h := congrArg (fun y : FiniteAdeleRing (𝓞 ℚ) ℚ => y v) (Units.inv_mul x)
  have h' : ((x⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v *
      (x : FiniteAdeleRing (𝓞 ℚ) ℚ) v = 1 := h
  rw [h', map_one]

private lemma natCast_ne (L : ℕ) (hL : 0 < L) (v : H.P ℚ) : (L : H.Kv v) ≠ 0 := by
  exact_mod_cast hL.ne'

private lemma v_natCast_of_not_bad (L : ℕ) (v : H.P ℚ) (h : ¬ Bad L v) : Valued.v (L : H.Kv v) = 1 := by
  have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) v (L : 𝓞 ℚ)
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 h] at h2
  exact_mod_cast h2

private lemma finite_bad (L : ℕ) (hL : 0 < L) : {v : H.P ℚ | Bad L v}.Finite := by
  have hne : Ideal.span {(L : 𝓞 ℚ)} ≠ 0 := by
    simpa [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hL.ne'
  refine (Ideal.finite_factors hne).subset fun v hv => ?_
  exact Ideal.dvd_span_singleton.2 hv

private lemma nhds_cong (L : ℕ) (hL : 0 < L) (v : H.P ℚ) :
    {x : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ | Valued.v ((x : FiniteAdeleRing (𝓞 ℚ) ℚ) v - 1) ≤ Valued.v (L : H.Kv v)} ∈
      𝓝 (1 : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) := by
  have hB : IsOpen {y : H.Kv v | Valued.v y ≤ Valued.v (L : H.Kv v)} := by
    have : {y : H.Kv v | Valued.v y ≤ Valued.v (L : H.Kv v)} =
        {y | Valued.v.restrict y ≤ Valued.v.restrict (L : H.Kv v)} := by
      ext y
      simp only [Set.mem_ofPred_eq, Valuation.restrict_le_iff]
    rw [this]
    exact Valued.isOpen_closedBall _ (by simp [natCast_ne L hL v])
  have he : Continuous fun y : FiniteAdeleRing (𝓞 ℚ) ℚ => y v := RestrictedProduct.continuous_eval v
  have hf : Continuous fun x : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ => (x : FiniteAdeleRing (𝓞 ℚ) ℚ) v - 1 :=
    (he.comp Units.continuous_val).sub continuous_const
  refine (hB.preimage hf).mem_nhds ?_
  have h0 : ((1 : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v - 1 = 0 := sub_self _
  change Valued.v (((1 : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v - 1) ≤ _
  rw [h0, map_zero]
  exact zero_le'

theorem UpperTheory.finiteIdele_congruenceVolume_pos :
    ∀ L : ℕ, 0 < L → 0 < cT L := by
  intro L hL
  set S : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ := (fun u => (IdeleGroup.prodEquiv ℚ).symm (1, u)) ⁻¹' TT L with hS
  have hcT : cT L = (finiteIdeleMeasure ℚ S).toReal := rfl
  have hsub : S ⊆ (finiteIntegralUnits ℚ : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) := by
    intro x hx
    have hu : ∀ v : H.P ℚ, Valued.v ((x : FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1 := fun v => hx.1.2 v
    refine (mem_finiteIntegralUnits ℚ).2 fun v => ?_
    have hi := inv_mul_at x v
    rw [hu v, mul_one] at hi
    exact ⟨(HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 (hu v).le,
      (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 hi.le⟩
  have hnhds : S ∈ 𝓝 (1 : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) := by
    have h1 : (finiteIntegralUnits ℚ : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) ∈ 𝓝 (1 : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :=
      (isOpen_finiteIntegralUnits ℚ).mem_nhds (one_mem _)
    have h2 := (Filter.biInter_mem (finite_bad L hL)).2 fun v (_ : Bad L v) => nhds_cong L hL v
    filter_upwards [h1, h2] with x hx hc
    obtain hxi := (mem_finiteIntegralUnits ℚ).1 hx
    have hle : ∀ v : H.P ℚ, Valued.v ((x : FiniteAdeleRing (𝓞 ℚ) ℚ) v) ≤ 1 := fun v =>
      (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 (hxi v).1
    have hle' : ∀ v : H.P ℚ, Valued.v (((x⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v) ≤ 1 :=
      fun v => (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 (hxi v).2
    refine ⟨⟨ef_fst x, fun v => ?_⟩, fun v => ?_⟩
    · exact eq_one_of_mul'' (hle v) (hle' v) (by rw [mul_comm]; exact inv_mul_at x v)
    · have hcp : H.cp v ((ef x : (A ℚ)ˣ) : A ℚ) - 1 = (x : FiniteAdeleRing (𝓞 ℚ) ℚ) v - 1 := rfl
      change Valued.v (H.cp v (((ef x : (A ℚ)ˣ) : A ℚ) - 1)) ≤ _
      rw [map_sub, map_one, hcp]
      by_cases hb : Bad L v
      · exact Set.mem_iInter₂.1 hc v hb
      · rw [v_natCast_of_not_bad L v hb]
        refine (Valuation.map_sub _ _ _).trans (max_le (hle v) ?_)
        rw [map_one]
  rw [hcT]
  refine ENNReal.toReal_pos (Measure.measure_pos_of_mem_nhds _ hnhds).ne' ?_
  refine ((measure_mono hsub).trans_lt ?_).ne
  rw [finiteIdeleMeasure_finiteIntegralUnits]
  exact ENNReal.one_lt_top
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem rhoB (p : MvPolynomial (Fin 2) ℂ) :
    Measurable (fun t : ℝ => MvPolynomial.eval ![(Real.sin t : ℂ), (Real.cos t : ℂ)] p) ∧
      ∃ C : ℝ, ∀ t : ℝ, ‖MvPolynomial.eval ![(Real.sin t : ℂ), (Real.cos t : ℂ)] p‖ ≤ C := by
  have hc : Continuous fun x : Fin 2 → ℂ => MvPolynomial.eval x p := MvPolynomial.continuous_eval p
  have hv : Continuous fun t : ℝ => (![(Real.sin t : ℂ), (Real.cos t : ℂ)] : Fin 2 → ℂ) := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact Complex.continuous_ofReal.comp Real.continuous_sin
    · exact Complex.continuous_ofReal.comp Real.continuous_cos
  refine ⟨(hc.comp hv).measurable, ?_⟩
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Fin 2 → ℂ) 1).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, fun t => hC _ ?_⟩
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  fin_cases i
  · show ‖((Real.sin t : ℝ) : ℂ)‖ ≤ 1
    rw [Complex.norm_real]
    exact Real.abs_sin_le_one t
  · show ‖((Real.cos t : ℝ) : ℂ)‖ ≤ 1
    rw [Complex.norm_real]
    exact Real.abs_cos_le_one t

private theorem It_ne {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) (χ : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ) (s : ℂ) (hs : 4 < s.re) (t : ℝ)
    (h : It D χ φ s t ≠ 0) : ∃ r t : ℝ, r ≠ 0 ∧ Wo D φ (em E (aE (iy r) * rot t)) ≠ 0 := by
  by_contra hn
  push_neg at hn
  refine h ?_
  unfold It
  have : ∀ y : ℝ, Wo D φ (em E (aE (iy y) * rot t)) * ((χ.1 (iy y) : ℂˣ) : ℂ) * (y : ℂ) ^ 0 * ((|y| : ℝ) : ℂ) ^ (s - 2) = 0 := by
    intro y
    by_cases hy : y = 0
    · subst hy
      have : s - 2 ≠ 0 := fun h0 => by
        have := congrArg Complex.re h0
        simp at this
        linarith
      simp [Complex.zero_cpow this]
    · rw [hn y t hy]
      simp
  simp only [this, integral_zero]

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.fac_of :
    Fac := by
  intro E _ _ _ D P ω χ hCen hU hχω M L N hχ
  by_cases hLN : 0 < L ∧ 0 < N
  swap
  · refine ⟨1, one_ne_zero, fun φ _ hG => ?_⟩
    exact absurd ⟨Nat.pos_of_dvd_of_pos hG.dvd hG.pos, hG.pos⟩ hLN
  obtain ⟨hL, hN⟩ := hLN
  have hcK := UpperTheory.congruenceSubgroup_volume_pos M N hN
  have hcL := UpperTheory.finiteIdele_congruenceVolume_pos L hL
  have hcN := UpperTheory.finiteIdele_congruenceVolume_pos N hN
  have hpi := Real.pi_pos
  refine ⟨((cK M N / (2 * Real.pi) : ℝ) : ℂ) * (cT L : ℂ) * (cT N : ℂ), ?_, ?_⟩
  · have h1 : ((cK M N / (2 * Real.pi) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (div_pos hcK (by positivity)).ne'
    have h2 : (cT L : ℂ) ≠ 0 := by exact_mod_cast hcL.ne'
    have h3 : (cT N : ℂ) ≠ 0 := by exact_mod_cast hcN.ne'
    exact mul_ne_zero (mul_ne_zero h1 h2) h3
  intro φ hA hG a hIs e p hp s hs hsum
  obtain ⟨μ, hμ, hco⟩ := UpperTheory.exists_whittaker_hecke_eigenvalues_and_coeff_eq_convolution E D P ω χ hCen hU hχω L N hχ φ hA hG a hIs
  have hY := UpperTheory.has_sum_twisted_zeta_integral_dirichlet_series E D P ω χ hCen hU hχω L N hχ φ hA hG μ hμ s hs
  obtain ⟨hYm, C, hC⟩ := UpperTheory.measurable_and_bounded_twisted_zeta_integral_rotation E D P ω χ hCen hU hχω L N hχ φ hA hG s hs
  obtain ⟨hρm, C', hC'⟩ := rhoB p
  set ρ : ℝ → ℂ := fun t => MvPolynomial.eval ![(Real.sin t : ℂ), (Real.cos t : ℂ)] p with hρ
  set Z0 : ℂ := (cT N : ℂ) * LSeries (sqN N) s * ((Real.pi : ℂ) ^ (-(s + e)) * Complex.Gamma (s + e)) with hZ0
  set G0 : ℂ := (Real.pi : ℂ) ^ (-(s + e)) * Complex.Gamma (s + e) with hG0
  have e1 : Zu D M χ φ (PhiN N p) s = ∫ k, Yt D χ φ s (gl k) * Zr N p s k ∂M.κ := by
    unfold Zu Yt Zr
    refine integral_congr_ae (Eventually.of_forall fun k => ?_)
    exact integral_mul_const _ _
  have e2 : ∫ k, Yt D χ φ s (gl k) * Zr N p s k ∂M.κ =
      ((cK M N / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (0 : ℝ)..2 * Real.pi, Yt D χ φ s (rot t) * (Z0 * ρ t) := by
    refine UpperTheory.integral_maxCompact_eq_circle_average M N hN _ (fun t => Yt D χ φ s (rot t) * (Z0 * ρ t)) (hYm.mul (measurable_const.mul hρm))
      ⟨C * (‖Z0‖ * C'), fun t => ?_⟩ (fun k hk hn => ?_) (fun k hk hS t h0 h1 => ?_)
    · rw [norm_mul, norm_mul]
      have h0 : 0 ≤ C := (norm_nonneg _).trans (hC t)
      exact mul_le_mul (hC t) (mul_le_mul_of_nonneg_left (hC' t) (norm_nonneg _))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) h0
    · show Yt D χ φ s (gl k) * Zr N p s k = 0
      rw [UpperTheory.zeta_integral_eq_zero_of_mem_maximal_compact_not_mem_level N hN p s k hk hn, mul_zero]
    · show Yt D χ φ s (gl k) * Zr N p s k = _
      rw [UpperTheory.zeta_integral_eq_lseries_mul_gamma_mul_eval_of_mem_level N hN e p hp s hs k hk hS t h0 h1,
        UpperTheory.twisted_zeta_integral_at_compact_eq_at_rotation E D P ω χ hCen hU hχω L N hχ φ hA hG s k hk hS t h0 h1]
  have eM : Mk D χ 0 φ p s = ∫ t in (0 : ℝ)..2 * Real.pi, ρ t * It D χ φ s t := rfl
  rw [e1, e2, eM]
  by_cases hI : ∀ t, It D χ φ s t = 0
  · have hY0 : ∀ t, Yt D χ φ s (rot t) = 0 := fun t => by
      have := hY t
      simp only [hI t, mul_zero] at this
      exact this.unique hasSum_zero
    simp [hY0, hI]
  push_neg at hI
  obtain ⟨t₀, ht₀⟩ := hI
  set u : {n : ℕ // 0 < n ∧ n.Coprime N} → ℂ := fun n => μ n * ((χ.1 (pin n) : ℂˣ) : ℂ) * (n : ℂ) ^ (1 - s) with hu
  have hcL' : (cT L : ℂ) ≠ 0 := by exact_mod_cast hcL.ne'
  have hus : Summable u := by
    have h1 := (hY t₀).summable
    have h2 : Summable fun n => u n * ((cT L : ℂ) * It D χ φ s t₀) := by
      refine h1.congr fun n => ?_
      simp only [hu]
      ring
    exact (summable_mul_right_iff (mul_ne_zero hcL' ht₀)).1 h2
  obtain ⟨hbS, hbL⟩ := UpperTheory.lseries_twisted_coeff_eq_tsum_coprime_of_summable N χ μ s hus
  have hYt : ∀ t, Yt D χ φ s (rot t) = (cT L : ℂ) * (∑' n, u n) * It D χ φ s t := fun t => by
    refine (hY t).unique ?_
    have := (hus.hasSum.mul_left (cT L : ℂ)).mul_right (It D χ φ s t)
    exact this
  have hco' := hco (It_ne D χ φ s hs t₀ ht₀)
  have hLs : LSeries a s = (∑' n, u n) * LSeries (sqN N) s := by
    rw [LSeries_congr (fun {n} hn => hco' n hn) s, LSeries_convolution' hbS (UpperTheory.lseries_summable_sq_coeff_of_four_lt_re N s hs), hbL]
  have e3 : ∫ t in (0 : ℝ)..2 * Real.pi, Yt D χ φ s (rot t) * (Z0 * ρ t) =
      ((cT L : ℂ) * (∑' n, u n) * Z0) * ∫ t in (0 : ℝ)..2 * Real.pi, ρ t * It D χ φ s t := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    show Yt D χ φ s (rot t) * (Z0 * ρ t) = _
    rw [hYt t]
    ring
  rw [e3, hLs, hZ0]
  ring
