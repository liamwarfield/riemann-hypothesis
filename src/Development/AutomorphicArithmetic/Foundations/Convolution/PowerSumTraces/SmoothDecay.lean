module

public import Development.AutomorphicArithmetic.TwistedTraces.CuspDecayTensConvRealSmoothT
public import GroundTheory.AutomorphicForms.L2LocalComponents.ArchBump

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.TwistedTraces.ExistsSumTensOfIsLeftSmooth
section -- merged from Development.AutomorphicArithmetic.TwistedTraces.ExistsSmoothTKbarEqRestriction
section -- merged from Development.AutomorphicArithmetic.TwistedTraces.ExistsSmoothArchCutoffKbarEqOne
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped ContDiff

private theorem frob_diag {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (M : Matrix (Fin n) (Fin n) 𝕜) (e : 𝕜) (r : ℝ)
    (he : ‖e‖ = r) : frobSq (M * Matrix.diagonal fun _ => e) = r ^ 2 * frobSq M := by
  simp only [frobSq, Matrix.mul_diagonal, norm_mul, mul_pow, he, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

private noncomputable def lam (K : Type) [Field K] [NumberField K] (n : ℕ) (s : {r : ℝ // 0 < r}) : ℝ :=
  ((rpowHom ((n * Module.finrank ℚ K : ℝ))⁻¹ s : {r : ℝ // 0 < r}) : ℝ)

private theorem lam_pos (K : Type) [Field K] [NumberField K] (n : ℕ) (s : {r : ℝ // 0 < r}) : 0 < lam K n s :=
  (rpowHom ((n * Module.finrank ℚ K : ℝ))⁻¹ s).2

private theorem infAt_zInf (K : Type) [Field K] [NumberField K] (n : ℕ) (s : {r : ℝ // 0 < r})
    (w : InfinitePlace K) : ∃ u : w.Completion, ‖u‖ = lam K n s ∧ ∀ a b : Fin n,
      Reduction.infAt w (infEmb K n (zInf K n s)) a b = if a = b then u else 0 := by
  refine ⟨(GroundTheory.Global.IdeleGroup.infiniteProj w (posIdele (K := K) (lam K n s) (lam_pos K n s)) : (w.Completion)ˣ), ?_, fun a b => ?_⟩
  · rw [GroundTheory.Global.IdeleGroup.coe_infiniteProj]
    exact norm_posIdele_infinite _ _ w
  · have e : centralSection K n s = diagUnits n fun _ => posIdele (K := K) (lam K n s) (lam_pos K n s) := rfl
    rw [infEmb_zInf, e, infAt_diagUnits, coe_diagUnits, Matrix.diagonal_apply]

private theorem quad_mul_zInf (K : Type) [Field K] [NumberField K] (n : ℕ) (A : ArchMatrix K n)
    (s : {r : ℝ // 0 < r}) : archQuad (A * archVal (zInf K n s)) = lam K n s ^ 2 * archQuad A := by
  have hr : ∀ v : {w : InfinitePlace K // InfinitePlace.IsReal w}, ∃ e : ℝ, ‖e‖ = lam K n s ∧
      realCompM v (archVal (zInf K n s)) = Matrix.diagonal fun _ => e := by
    rintro ⟨w, hw⟩
    obtain ⟨u, hu, hab⟩ := infAt_zInf K n s w
    refine ⟨InfinitePlace.Completion.extensionEmbeddingOfIsReal hw u, ?_, ?_⟩
    · rw [← hu]
      exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) u
    · ext a b
      have h1 := congrArg (InfinitePlace.Completion.extensionEmbeddingOfIsReal hw) (hab a b)
      rw [infAt_infEmb_apply, extensionEmbeddingOfIsReal_symm] at h1
      simp only [realCompM_apply, Matrix.map_apply, realComp_apply, Matrix.diagonal_apply]
      rw [h1]
      split_ifs <;> simp
  have hc : ∀ v : {w : InfinitePlace K // InfinitePlace.IsComplex w}, ∃ e : ℂ, ‖e‖ = lam K n s ∧
      complexCompM v (archVal (zInf K n s)) = Matrix.diagonal fun _ => e := by
    rintro ⟨w, hw⟩
    obtain ⟨u, hu, hab⟩ := infAt_zInf K n s w
    refine ⟨InfinitePlace.Completion.extensionEmbedding w u, ?_, ?_⟩
    · rw [← hu]
      exact (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) u
    · ext a b
      have h1 := congrArg (InfinitePlace.Completion.extensionEmbedding w) (hab a b)
      rw [infAt_infEmb_apply, extensionEmbedding_symm _ hw] at h1
      simp only [complexCompM_apply, Matrix.map_apply, complexComp_apply, Matrix.diagonal_apply]
      rw [h1]
      split_ifs <;> simp
  simp only [archQuad, mul_add, Finset.mul_sum, map_mul]
  congr 1
  · refine Finset.sum_congr rfl fun v _ => ?_
    obtain ⟨e, he, hv⟩ := hr v
    rw [hv, frob_diag _ e _ he]
  · refine Finset.sum_congr rfl fun v _ => ?_
    obtain ⟨e, he, hv⟩ := hc v
    rw [hv, frob_diag _ e _ he]

private theorem quad_ne (K : Type) [Field K] [NumberField K] (n : ℕ) (hn : 0 < n) (a : archGroup K n) :
    archQuad (archVal a) ≠ 0 := by
  intro h
  have h0 := archQuad_eq_zero h
  have h1 : archVal a * archVal a⁻¹ = 1 := by
    rw [archVal, archVal, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one]
  rw [h0, zero_mul] at h1
  have h2 : (0 : mixedEmbedding.mixedSpace K) = 1 := by
    have h3 := congrFun (congrFun (congrArg mat h1) ⟨0, hn⟩) ⟨0, hn⟩
    rw [mat_zero, mat_one, Matrix.one_apply_eq] at h3
    exact h3
  obtain ⟨w⟩ : Nonempty (InfinitePlace K) := inferInstance
  by_cases hw : InfinitePlace.IsReal w
  · have h3 := congrArg (fun p : mixedEmbedding.mixedSpace K => p.1 ⟨w, hw⟩) h2
    exact zero_ne_one (α := ℝ) h3
  · have hw' := InfinitePlace.not_isReal_iff_isComplex.1 hw
    have h3 := congrArg (fun p : mixedEmbedding.mixedSpace K => p.2 ⟨w, hw'⟩) h2
    exact zero_ne_one (α := ℂ) h3

private theorem lam_exp (K : Type) [Field K] [NumberField K] (n : ℕ) (t : ℝ) :
    lam K n (GroundTheory.Global.expPos t) = Real.exp (t * (n * Module.finrank ℚ K : ℝ)⁻¹) := by
  change (Real.exp t) ^ ((n * Module.finrank ℚ K : ℝ))⁻¹ = _
  rw [← Real.exp_mul]

private noncomputable def lq (K : Type) [Field K] [NumberField K] (n : ℕ) (a : archGroup K n) : ℝ :=
  Real.log (archQuad (archVal a))

private theorem lq_mul (K : Type) [Field K] [NumberField K] (n : ℕ) (hn : 0 < n) (a : archGroup K n) (t : ℝ) :
    lq K n (a * zInf K n (GroundTheory.Global.expPos t)) = lq K n a + 2 * (n * Module.finrank ℚ K : ℝ)⁻¹ * t := by
  have e : archVal (a * zInf K n (GroundTheory.Global.expPos t)) = archVal a * archVal (zInf K n (GroundTheory.Global.expPos t)) := rfl
  rw [lq, e, quad_mul_zInf, lam_exp, Real.log_mul (by positivity) (quad_ne K n hn a), Real.log_pow, Real.log_exp, lq]
  push_cast
  ring

private theorem continuous_lq (K : Type) [Field K] [NumberField K] (n : ℕ) (hn : 0 < n) :
    Continuous (lq K n) :=
  Continuous.log ((contDiff_archQuad (K := K) (n := n)).continuous.comp continuous_archVal) (quad_ne K n hn)

theorem UpperTheory.exists_smooth_archCutoff_kbar_eq_one :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n →
        ∃ χ : archGroup K n → ℝ, (isExpLieAlgebra K n).IsSmoothFun (fun A => (χ A : ℂ)) ∧
          (∀ A, kbar (fun g => (χ g : ℂ)) A = 1) ∧
          ∀ C : Set (G1 K n), IsCompact C → ∃ D : Set (archGroup K n), IsCompact D ∧
            ∀ A, χ A ≠ 0 → archP K n A ∈ C → A ∈ D := by
  intro K _ _ n hn
  set d : ℝ := (n * Module.finrank ℚ K : ℝ) with hd
  have hd0 : 0 < d := by
    have : 0 < Module.finrank ℚ K := Module.finrank_pos
    have h2 : (0 : ℝ) < n := Nat.cast_pos.2 hn
    have h3 : (0 : ℝ) < Module.finrank ℚ K := Nat.cast_pos.2 this
    positivity
  set β : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩ with hβ
  set h : ℝ → ℝ := β.normed volume with hh
  set c : ℝ := 2 * d⁻¹ with hc
  have hc0 : 0 < c := by positivity
  refine ⟨fun A => c * h (lq K n A), ?_, fun A => ?_, fun C hC => ?_⟩
  · rw [IsExpLieAlgebra.isSmoothFun_iff]
    intro g
    have hY : ContDiff ℝ ∞ (fun Y : archLie K n => (Y : ArchMatrix K n)) :=
      (Submodule.subtypeL (archLie K n)).contDiff
    have hexp : ContDiff ℝ ∞ (NormedSpace.exp : ArchMatrix K n → ArchMatrix K n) :=
      contDiff_exp ℝ _
    have hq : ContDiff ℝ ∞ (archQuad : ArchMatrix K n → ℝ) := contDiff_archQuad.of_le le_top
    have e : (fun Y : archLie K n => lq K n (g * (isExpLieAlgebra K n).expG Y)) = fun Y : archLie K n =>
        Real.log (archQuad (archVal g * NormedSpace.exp (Y : ArchMatrix K n))) := by
      funext Y
      simp only [lq, archVal, Subgroup.coe_mul, Units.val_mul, IsExpLieAlgebra.coe_expG]
    have hl : ContDiff ℝ ∞ (fun Y : archLie K n => lq K n (g * (isExpLieAlgebra K n).expG Y)) := by
      rw [e]
      refine ContDiff.log (hq.comp (contDiff_const.mul (hexp.comp hY))) fun Y => ?_
      have := quad_ne K n hn (g * (isExpLieAlgebra K n).expG Y)
      simpa only [archVal, Subgroup.coe_mul, Units.val_mul, IsExpLieAlgebra.coe_expG] using this
    exact Complex.ofRealCLM.contDiff.comp (contDiff_const.mul (β.contDiff_normed.comp hl))
  · have hemb : MeasurableEmbedding GroundTheory.Global.expPos :=
      GroundTheory.Global.expPosHomeomorph.measurableEmbedding
    rw [kbar, GroundTheory.Global.posRealMeasure_eq_map_expPos, hemb.integral_map]
    have e1 : ∀ t : ℝ, ((c * h (lq K n (A * zInf K n (GroundTheory.Global.expPos t))) : ℝ) : ℂ) =
        ((c * h (lq K n A + c * t) : ℝ) : ℂ) := fun t => by
      rw [lq_mul K n hn]
    simp only [e1]
    rw [integral_complex_ofReal, integral_const_mul]
    have e2 : ∫ t, h (lq K n A + c * t) = |c⁻¹| • ∫ y, h (lq K n A + y) :=
      Measure.integral_comp_mul_left (fun y => h (lq K n A + y)) c
    rw [e2, integral_add_left_eq_self h (lq K n A), hh, β.integral_normed, abs_of_pos (inv_pos.2 hc0),
      smul_eq_mul, mul_one, mul_inv_cancel₀ hc0.ne']
    simp
  · set C' : Set (archGroup K n) := (fun x : G1 K n => infPart K n (x : AdelicGLn.AdelicGL K n)) '' C with hC'
    have hC'c : IsCompact C' := hC.image (continuous_infPart.comp continuous_subtype_val)
    obtain ⟨M, hM⟩ := hC'c.exists_bound_of_continuousOn (continuous_lq K n hn).continuousOn
    set R : ℝ := (2 + M) / c with hR
    refine ⟨(fun p : archGroup K n × ℝ => p.1 * zInf K n (GroundTheory.Global.expPos p.2)) '' (C' ×ˢ Set.Icc (-R) R),
      (hC'c.prod isCompact_Icc).image
        (continuous_fst.mul (continuous_zInf.comp (GroundTheory.Global.expPosHomeomorph.continuous.comp continuous_snd))),
      fun A hA hAC => ?_⟩
    set r := detA K n A with hr
    set a := infPart K n (archP K n A : AdelicGLn.AdelicGL K n) with ha
    have haC : a ∈ C' := ⟨_, hAC, rfl⟩
    have hr' : GroundTheory.Global.expPos (Real.log r) = r := Subtype.ext (Real.exp_log r.2)
    have hAa : A = a * zInf K n (GroundTheory.Global.expPos (Real.log r)) := by
      rw [hr', ha, infPart_archP, inv_mul_cancel_right]
    have hsup : lq K n A ∈ Metric.ball (0 : ℝ) 2 := by
      have h1 : h (lq K n A) ≠ 0 := right_ne_zero_of_mul hA
      have h2 : lq K n A ∈ Function.support h := h1
      rw [hh, β.support_normed_eq] at h2
      exact h2
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hsup
    have hl := lq_mul K n hn a (Real.log r)
    rw [← hAa] at hl
    have hMa := hM a haC
    rw [Real.norm_eq_abs] at hMa
    have hct : |c * Real.log r| ≤ 2 + M := by
      have e3 : c * Real.log r = lq K n A - lq K n a := by rw [hl, hc, hd]; ring
      rw [e3]
      exact (abs_sub _ _).trans (by linarith)
    have ht : |Real.log r| ≤ R := by
      rw [hR, le_div_iff₀ hc0]
      rwa [abs_mul, abs_of_pos hc0, mul_comm] at hct
    exact ⟨(a, Real.log r), ⟨haC, abs_le.1 ht⟩, hAa.symm⟩
end

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped ContDiff

theorem UpperTheory.exists_smoothT_kbar_eq_restriction :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (a : CC K n) (x₀ : G1 K n),
        (isExpLieAlgebra K n).IsSmoothFun (fun A : archGroup K n => a (archP K n A * x₀)) →
        ∃ F : TI K n, SmoothT F ∧ ∀ A, kbar F A = a (archP K n A * x₀) := by
  intro K _ _ n hn a x₀ ha
  obtain ⟨χ, hχs, hχ1, hχc⟩ := UpperTheory.exists_smooth_archCutoff_kbar_eq_one K n hn
  have hχcont : Continuous fun A : archGroup K n => (χ A : ℂ) := by
    letI := (isExpLieAlgebra K n).chartedSpace
    exact ContMDiff.continuous hχs
  have hcont : Continuous fun A : archGroup K n => (χ A : ℂ) * a (archP K n A * x₀) :=
    hχcont.mul (a.continuous.comp (continuous_archP.mul continuous_const))
  have hC : IsCompact ((fun g : G1 K n => g * x₀⁻¹) '' tsupport a) :=
    a.hasCompactSupport.isCompact.image (continuous_id.mul continuous_const)
  obtain ⟨D, hD, hDm⟩ := hχc _ hC
  have hcs : HasCompactSupport fun A : archGroup K n => (χ A : ℂ) * a (archP K n A * x₀) := by
    refine HasCompactSupport.intro hD fun A hA => ?_
    by_contra hne
    have h1 : χ A ≠ 0 := fun h0 => hne (by rw [h0, Complex.ofReal_zero, zero_mul])
    have h2 : a (archP K n A * x₀) ≠ 0 := fun h0 => hne (by rw [h0, mul_zero])
    exact hA (hDm A h1 ⟨archP K n A * x₀, subset_tsupport _ h2, by simp⟩)
  refine ⟨⟨⟨_, hcont⟩, hcs⟩, ?_, fun A => ?_⟩
  · refine ((isExpLieAlgebra K n).isSmoothFun_iff).2 fun g => ?_
    exact ContDiff.mul (((isExpLieAlgebra K n).isSmoothFun_iff).1 hχs g)
      (((isExpLieAlgebra K n).isSmoothFun_iff).1 ha g)
  · have h1 := hχ1 A
    unfold kbar at h1 ⊢
    have h2 : ∀ s, (χ (A * zInf K n s) : ℂ) * a (archP K n (A * zInf K n s) * x₀) =
        (χ (A * zInf K n s) : ℂ) * a (archP K n A * x₀) := fun s => by
      rw [archimedeanProjection_mul_positiveScalar hn]
    show ∫ s, (χ (A * zInf K n s) : ℂ) * a (archP K n (A * zInf K n s) * x₀) ∂_ = _
    simp_rw [h2]
    rw [integral_mul_const, h1, one_mul]
end

section -- merged from Development.AutomorphicArithmetic.TwistedTraces.ExistsFiniteBasisLeftInvariantCompactSupport
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped ContDiff

theorem UpperTheory.exists_finite_basis_leftInvariant_compactSupport :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (V : Subgroup G),
        IsOpen (V : Set G) → IsCompact (V : Set G) → ∀ S : Set G, IsCompact S →
        ∃ (m : ℕ) (b : Fin m → G) (e : Fin m → CompactlySupportedContinuousMap G ℂ),
          (∀ j, ∀ v ∈ V, ∀ h, e j (v * h) = e j h) ∧
          ∀ f : G → ℂ, (∀ v ∈ V, ∀ h, f (v * h) = f h) → (∀ h, h ∉ S → f h = 0) →
            ∀ h, f h = ∑ j, e j h * f (b j) := by
  intro G _ _ _ _ V hVo hVc S hS
  classical
  have hVcl : IsClosed (V : Set G) := Subgroup.isClosed_of_isOpen V hVo

  let W : G → Set G := fun b => {h | b * h⁻¹ ∈ V}
  have hWpre : ∀ b, W b = (fun h : G => b * h⁻¹) ⁻¹' (V : Set G) := fun b => rfl
  have hcont : ∀ b : G, Continuous (fun h : G => b * h⁻¹) := fun b =>
    continuous_const.mul continuous_inv
  have hWo : ∀ b, IsOpen (W b) := fun b => by
    rw [hWpre]; exact hVo.preimage (hcont b)
  have hWcl : ∀ b, IsClosed (W b) := fun b => by
    rw [hWpre]; exact hVcl.preimage (hcont b)
  have hWself : ∀ b, b ∈ W b := fun b => by
    show b * b⁻¹ ∈ V
    simpa using V.one_mem
  have hWK : ∀ b, W b ⊆ (fun v : G => v⁻¹ * b) '' (V : Set G) := fun b h hh =>
    ⟨b * h⁻¹, hh, by group⟩
  have hKc : ∀ b, IsCompact ((fun v : G => v⁻¹ * b) '' (V : Set G)) := fun b =>
    hVc.image (continuous_inv.mul continuous_const)
  have hWinv : ∀ b, ∀ v ∈ V, ∀ h, v * h ∈ W b ↔ h ∈ W b := fun b v hv h => by
    show b * (v * h)⁻¹ ∈ V ↔ b * h⁻¹ ∈ V
    have : b * (v * h)⁻¹ = b * h⁻¹ * v⁻¹ := by group
    rw [this]
    exact V.mul_mem_cancel_right (V.inv_mem hv)

  let E : G → CompactlySupportedContinuousMap G ℂ := fun b =>
    { toFun := (W b).indicator (fun _ => (1 : ℂ))
      continuous_toFun := (IsClopen.continuous_indicator ⟨hWcl b, hWo b⟩ continuous_const)
      hasCompactSupport' := by
        refine HasCompactSupport.intro (hKc b) (fun x hx => ?_)
        exact Set.indicator_of_notMem (fun hxW => hx (hWK b hxW)) _ }
  have hE : ∀ b h, E b h = (W b).indicator (fun _ => (1 : ℂ)) h := fun _ _ => rfl

  let q : G → Quotient (QuotientGroup.rightRel V) := fun h => Quotient.mk _ h
  have hq : ∀ x y : G, q x = q y ↔ x ∈ W y := fun x y => by
    show Quotient.mk _ x = Quotient.mk _ y ↔ y * x⁻¹ ∈ V
    rw [Quotient.eq]
    exact QuotientGroup.rightRel_apply
  obtain ⟨t, -, ht⟩ := hS.elim_nhds_subcover W (fun x _ => (hWo x).mem_nhds (hWself x))
  let T : Finset (Quotient (QuotientGroup.rightRel V)) := t.image q
  let ε := T.equivFin
  let b : Fin T.card → G := fun j => (ε.symm j).1.out
  have hqb : ∀ j, q (b j) = (ε.symm j).1 := fun j => Quotient.out_eq _
  refine ⟨T.card, b, fun j => E (b j), ?_, ?_⟩
  · intro j v hv h
    rw [hE, hE]
    by_cases hh : h ∈ W (b j)
    · rw [Set.indicator_of_mem hh, Set.indicator_of_mem ((hWinv _ v hv h).2 hh)]
    · rw [Set.indicator_of_notMem hh,
        Set.indicator_of_notMem (fun h' => hh ((hWinv _ v hv h).1 h'))]
  · intro f hfV hfS h
    have hfW : ∀ c x, x ∈ W c → f x = f c := fun c x hx => by
      have := hfV (c * x⁻¹) hx x
      simpa using this.symm
    by_cases hT : q h ∈ T
    · let j0 : Fin T.card := ε ⟨q h, hT⟩
      have hj0 : q (b j0) = q h := by
        rw [hqb]; simp [j0]
      have hmem : h ∈ W (b j0) := (hq _ _).1 hj0.symm
      rw [Finset.sum_eq_single j0]
      · rw [hE, Set.indicator_of_mem hmem, one_mul]
        exact hfW _ _ hmem
      · intro j _ hj
        have hnot : h ∉ W (b j) := fun hm => by
          apply hj
          have h1 : (ε.symm j).1 = q h := by rw [← hqb]; exact ((hq _ _).2 hm).symm
          have h2 : ε.symm j = ⟨q h, hT⟩ := Subtype.ext h1
          simp [j0, ← h2]
        rw [hE, Set.indicator_of_notMem hnot, zero_mul]
      · intro hj; exact absurd (Finset.mem_univ _) hj
    · have hhS : h ∉ S := fun hs => by
        have := ht hs
        simp only [Set.mem_iUnion] at this
        obtain ⟨x, hx, hxW⟩ := this
        exact hT (Finset.mem_image.2 ⟨x, hx, ((hq _ _).2 hxW).symm⟩)
      rw [hfS h hhS]
      symm
      refine Finset.sum_eq_zero (fun j _ => ?_)
      have hnot : h ∉ W (b j) := fun hm => hT (by
        rw [(hq _ _).2 hm, hqb]; exact (ε.symm j).2)
      rw [hE, Set.indicator_of_notMem hnot, zero_mul]
end

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped ContDiff

private theorem split_pt {K : Type} [Field K] [NumberField K] {n : ℕ} (x : G1 K n) :
    x = archP K n (infPart K n (x : AdelicGLn.AdelicGL K n)) *
      MultiplicityOne.finProj K n (finPart K n (x : AdelicGLn.AdelicGL K n)) := by
  have h1 : retractOne (finEmb K n (finPart K n (x : AdelicGLn.AdelicGL K n))) =
      MultiplicityOne.finProj K n (finPart K n (x : AdelicGLn.AdelicGL K n)) := by
    ext1
    rfl
  rw [← h1, ← retract_infEmb, ← retractOne_mul, infEmb_infPart_mul_finEmb_finPart, retractOne_coe]

private theorem finPart_split {K : Type} [Field K] [NumberField K] {n : ℕ} (A : archGroup K n)
    (h : AdelicGLn.FiniteAdelicGL K n) :
    finPart K n ((archP K n A * MultiplicityOne.finProj K n h : G1 K n) : AdelicGLn.AdelicGL K n) = h := by
  have h1 : retractOne (finEmb K n h) = MultiplicityOne.finProj K n h := by
    ext1
    rfl
  rw [Subgroup.coe_mul, map_mul, finPart_archP, one_mul, ← h1, finPart_retract, finPart_finEmb]

theorem UpperTheory.exists_sum_tens_of_isLeftSmooth :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ a : CC K n, IsLeftSmooth a →
        ∃ (U : Subgroup (AdelicGLn.integralFiniteGL K n)) (_ : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)))
          (m : ℕ) (F : Fin m → TI K n) (e : Fin m → TF K n), (∀ j, SmoothT (F j)) ∧
          (∀ j, ∀ u ∈ U, ∀ h, e j ((u : AdelicGLn.FiniteAdelicGL K n) * h) = e j h) ∧ a = ∑ j, tens (F j) (e j) := by
  intro K _ _ n hn a ha
  obtain ⟨hsm, U, hU, hinv⟩ := ha
  have hVo : IsOpen (((finOpenSubgroup U hU).toSubgroup : Subgroup _) : Set (AdelicGLn.FiniteAdelicGL K n)) :=
    (finOpenSubgroup U hU).isOpen
  have hVc : IsCompact (((finOpenSubgroup U hU).toSubgroup : Subgroup _) : Set (AdelicGLn.FiniteAdelicGL K n)) :=
    isCompact_openSubgroupOf U hU
  have hS : IsCompact ((fun x : G1 K n => finPart K n (x : AdelicGLn.AdelicGL K n)) '' tsupport a) :=
    a.hasCompactSupport.isCompact.image (continuous_finPart.comp continuous_subtype_val)
  obtain ⟨m, b, e, heV, hE⟩ := UpperTheory.exists_finite_basis_leftInvariant_compactSupport _ (finOpenSubgroup U hU).toSubgroup hVo hVc _ hS
  choose F hF hFk using fun j => UpperTheory.exists_smoothT_kbar_eq_restriction K n hn a (MultiplicityOne.finProj K n (b j)) (hsm _)
  refine ⟨U, hU, m, F, e, hF, fun j u hu h => heV j _ (coe_mem_openSubgroupOf U hU hu) h, ?_⟩
  ext x
  have hsum : ∀ (s : Finset (Fin m)), (∑ j ∈ s, tens (F j) (e j)) x = ∑ j ∈ s, tens (F j) (e j) x := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, CompactlySupportedContinuousMap.add_apply, ih]
  rw [hsum Finset.univ]
  simp only [(UpperTheory.ConvolutionTheory.Tf.tensApply K n hn _ _).1, tensFun, hFk]
  have hfV : ∀ v ∈ (finOpenSubgroup U hU).toSubgroup, ∀ h,
      a (archP K n (infPart K n (x : AdelicGLn.AdelicGL K n)) * MultiplicityOne.finProj K n (v * h)) =
        a (archP K n (infPart K n (x : AdelicGLn.AdelicGL K n)) * MultiplicityOne.finProj K n h) := by
    intro v hv h
    have hv' : v ∈ (finOpenSubgroup U hU : Set (AdelicGLn.FiniteAdelicGL K n)) := hv
    rw [coe_openSubgroupOf] at hv'
    obtain ⟨u, hu, rfl⟩ := hv'
    rw [map_mul (MultiplicityOne.finProj K n), MultiplicityOne.finProj_eq_finOne, ← mul_assoc, archimedeanProjection_mul_finiteEmbedding_comm, mul_assoc, hinv u hu]
  have hfS : ∀ h, h ∉ (fun x : G1 K n => finPart K n (x : AdelicGLn.AdelicGL K n)) '' tsupport a →
      a (archP K n (infPart K n (x : AdelicGLn.AdelicGL K n)) * MultiplicityOne.finProj K n h) = 0 := by
    intro h hh
    by_contra hne
    exact hh ⟨_, subset_tsupport _ hne, finPart_split _ h⟩
  have key := hE (fun h => a (archP K n (infPart K n (x : AdelicGLn.AdelicGL K n)) * MultiplicityOne.finProj K n h))
    hfV hfS (finPart K n (x : AdelicGLn.AdelicGL K n))
  simp only [← split_pt x] at key
  rw [key]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]
end

section -- merged from Development.AutomorphicArithmetic.TwistedTraces.CuspDecayFinsetSum
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped ContDiff

private theorem rconv_add_fun {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n))
    [μ.IsHaarMeasure] (a b : CC K n) (φ : L2 μ) (x : G1 K n) :
    rconv (Gam K n) μ (a + b : CC K n) φ x =
      rconv (Gam K n) μ a φ x + rconv (Gam K n) μ b φ x := by
  unfold rconv
  rw [← integral_add (integrable_rconv (Gam K n) μ a φ x) (integrable_rconv (Gam K n) μ b φ x)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [CompactlySupportedContinuousMap.coe_add, Pi.add_apply, add_mul]

private theorem cuspDecay_zero {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n))
    [μ.IsHaarMeasure] : CuspDecay μ (0 : CC K n) := fun _ =>
  ⟨0, fun φ _ x => by simp [rconv]⟩

private theorem cuspDecay_add {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n))
    [μ.IsHaarMeasure] {a b : CC K n} (ha : CuspDecay μ a) (hb : CuspDecay μ b) :
    CuspDecay μ (a + b) := fun N' => by
  obtain ⟨C₁, h₁⟩ := ha N'
  obtain ⟨C₂, h₂⟩ := hb N'
  refine ⟨C₁ + C₂, fun φ hφ x => ?_⟩
  rw [rconv_add_fun, add_mul, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (h₁ φ hφ x) (h₂ φ hφ x))

theorem UpperTheory.cuspDecay_finset_sum :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure]
        (ι : Type) [Fintype ι] (f : ι → CC K n), (∀ i, CuspDecay μ (f i)) → CuspDecay μ (∑ i, f i) := by
  intro K _ _ n μ _ ι _ f hf
  exact Finset.sum_induction f (CuspDecay μ) (fun _ _ => cuspDecay_add μ) (cuspDecay_zero μ)
    (fun i _ => hf i)
end

section -- merged from Development.AutomorphicArithmetic.TwistedTraces.ExistsSumConvRealSmoothT
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped ContDiff

private noncomputable def mkL {K : Type} [Field K] [NumberField K] {n : ℕ} (L : ℂ →L[ℝ] ℂ) (f : TI K n) : TI K n :=
  ⟨⟨fun g => L (f g), L.continuous.comp f.continuous⟩, f.hasCompactSupport.comp_left (map_zero L)⟩

private theorem smoothT_mkL {K : Type} [Field K] [NumberField K] {n : ℕ} (L : ℂ →L[ℝ] ℂ) {f : TI K n}
    (hf : SmoothT f) : SmoothT (mkL L f) := by
  let _ := (isExpLieAlgebra K n).chartedSpace
  exact L.contDiff.comp_contMDiff hf

private noncomputable def reL : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.reCLM

private noncomputable def imL : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.imCLM

private theorem conv_split {K : Type} [Field K] [NumberField K] {n : ℕ}
    (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (a b : TI K n) (x : archGroup K n) :
    conv ν (mkL reL a) b x + conv ν (mkL imL a) (Complex.I • b) x = ∫ y, a y * b (y⁻¹ * x) ∂ν := by
  have hb : Continuous fun y : archGroup K n => b (y⁻¹ * x) := by fun_prop
  have i1 : Integrable (fun y => mkL reL a y * b (y⁻¹ * x)) ν :=
    ((mkL reL a).continuous.mul hb).integrable_of_hasCompactSupport
      (mkL reL a).hasCompactSupport.mul_right
  have i2 : Integrable (fun y => mkL imL a y * (Complex.I • b) (y⁻¹ * x)) ν :=
    ((mkL imL a).continuous.mul ((Complex.I • b).continuous.comp (by fun_prop))).integrable_of_hasCompactSupport
      (mkL imL a).hasCompactSupport.mul_right
  rw [conv_apply, conv_apply, ← integral_add i1 i2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show ((a y).re : ℂ) * b (y⁻¹ * x) + ((a y).im : ℂ) * (Complex.I * b (y⁻¹ * x)) = a y * b (y⁻¹ * x)
  have hz : ((a y).re : ℂ) + ((a y).im : ℂ) * Complex.I = a y := Complex.re_add_im _
  calc _ = (((a y).re : ℂ) + ((a y).im : ℂ) * Complex.I) * b (y⁻¹ * x) := by ring
    _ = _ := by rw [hz]

theorem UpperTheory.exists_sum_conv_real_smoothT :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ν : Measure (archGroup K n)) [ν.IsHaarMeasure]
        (F : TI K n), SmoothT F → ∃ (ι : Type) (_ : Fintype ι) (κ γ : ι → TI K n),
          (∀ i, SmoothT (κ i) ∧ ∀ g, (κ i g).im = 0) ∧ F = ∑ i, conv ν (κ i) (γ i) := by
  intro K _ _ n ν _ F hF
  obtain ⟨N, φ, ψ, h, e⟩ := dixmierMalliavin (isExpLieAlgebra K n) ν (fun g => F g) hF F.hasCompactSupport
  let _ := (isExpLieAlgebra K n).chartedSpace
  let a : Fin N → TI K n := fun i => ⟨⟨φ i, (h i).1.continuous⟩, (h i).2.1⟩
  let b : Fin N → TI K n := fun i => ⟨⟨ψ i, (h i).2.2.1.continuous⟩, (h i).2.2.2⟩
  have has : ∀ i, SmoothT (a i) := fun i => (h i).1
  refine ⟨Fin N × Bool, inferInstance,
    fun p => if p.2 then mkL imL (a p.1) else mkL reL (a p.1),
    fun p => if p.2 then Complex.I • b p.1 else b p.1, ?_, ?_⟩
  · rintro ⟨i, _ | _⟩
    · exact ⟨smoothT_mkL _ (has i), fun g => by simp [mkL, reL]⟩
    · exact ⟨smoothT_mkL _ (has i), fun g => by simp [mkL, imL]⟩
  · ext x
    have ex : F x = ∑ i, groupConv ν (φ i) (ψ i) x := by
      have := congrFun e x
      simpa [Finset.sum_apply] using this
    rw [ex, CompactlySupportedContinuousMap.sum_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_bool]
    simp only [if_true, Bool.false_eq_true, if_false]
    rw [add_comm, conv_split]
    rfl
end

section -- merged from Development.AutomorphicArithmetic.TwistedTraces.CuspDecayOfRankZero
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped ContDiff

theorem UpperTheory.cuspDecay_of_rank_zero :
    ∀ (K : Type) [Field K] [NumberField K] (μ : Measure (G1 K 0)) [μ.IsHaarMeasure] (a : CC K 0), CuspDecay μ a := by
  intro K _ _ μ _ a N'
  haveI : Subsingleton (AdelicGLn.AdelicGL K 0) :=
    ⟨fun x y => Units.ext (Subsingleton.elim _ _)⟩
  haveI : Subsingleton (G1 K 0) := ⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩
  obtain ⟨Ω₀, hΩ₁, hΩ₁B, t, ht, hsieg⟩ := exists_siegelSet (K := K) 0
  have hbasic : ∃ (C : ℝ) (N : ℕ), ∀ φ : Lp ℂ 2 (quotientMeasure (Gam K 0) μ), ∀ b ∈ Ω₀,
      ∀ (ρ : Fin 0 → ℝ) (hρ : ∀ i, 0 < ρ i),
      (∀ i j : Fin 0, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) →
      ∀ kk ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K 0)), ∀ x : G1 K 0,
      (x : AdelicGLn.AdelicGL K 0) = b * diagUnits 0 (fun i => posIdele (K := K) (ρ i) (hρ i)) * kk →
      ∀ R : ℝ, 1 ≤ R → (∀ i j : Fin 0, i < j → ρ i / ρ j ≤ R) →
      ‖rconv (Gam K 0) μ a φ x‖ ≤ C * Real.sqrt (R ^ N) * ‖φ‖ := by
    obtain ⟨Cc, N, hCc⟩ := exists_encard_le_siegel hΩ₁ ht a.hasCompactSupport
    have hf2 : ∫⁻ y, ‖a y‖ₑ ^ 2 ∂μ ≠ ⊤ := by
      have h := a.continuous.memLp_of_hasCompactSupport (μ := μ) (p := 2) a.hasCompactSupport
      rw [← L2Kernel.eLpNorm_two_sq]
      have hnorm := h.eLpNorm_lt_top
      rw [eLpNorm_eq_eLpNorm' (by norm_num) (by simp) h.aestronglyMeasurable,
        ENNReal.toReal_ofNat] at hnorm
      exact (ENNReal.pow_lt_top hnorm).ne
    let A := (∫⁻ y, ‖a y‖ₑ ^ 2 ∂μ).toReal
    have hA : 0 ≤ A := ENNReal.toReal_nonneg
    refine ⟨Real.sqrt (A * max Cc 0), N, ?_⟩
    intro φ b hb ρ hρ hsieg kk hkk x hx R hR1 hR
    obtain ⟨m, hmC, hm⟩ := hCc b hb ρ hρ hsieg kk hkk x hx R hR1 hR
    have hS : MeasurableSet ((fun y => x * y) '' tsupport (a : G1 K 0 → ℂ)) :=
      (a.hasCompactSupport.image (continuous_const_mul x)).measurableSet
    have h1 := enorm_rconv_sq_le (Gam K 0) μ a φ x hS (fun y hy => image_eq_zero_of_notMem_tsupport
      fun h' => hy ⟨x⁻¹ * y, h', by simp⟩) hm
    rw [← mul_assoc] at h1
    have h2 := norm_le_of_enorm_sq_le (ENNReal.mul_ne_top hf2 (by simp)) h1
    refine h2.trans ?_
    gcongr
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ← Real.sqrt_mul (mul_nonneg hA
      (le_max_right _ _))]
    refine Real.sqrt_le_sqrt ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hmC.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (pow_nonneg (by linarith) _))) hA
  obtain ⟨C₀, N, hC₀⟩ := hbasic
  have hq : 1 ≤ qht (1 : G1 K 0) := le_ciInf fun _ => AutomorphicForm.one_le_height _
  have hqN : qht (1 : G1 K 0) ^ N' ≠ 0 := (pow_pos (by linarith) N').ne'
  refine ⟨max C₀ 0 * qht (1 : G1 K 0) ^ N', fun φ _ x => ?_⟩
  obtain ⟨γ, hγ⟩ := hsieg (x : AdelicGLn.AdelicGL K 0)
  obtain ⟨b, hb, a', ⟨ρ, hρ, hs, rfl⟩, kk, hkk, -⟩ := hγ
  have h := hC₀ φ b hb ρ hρ hs kk hkk x (Subsingleton.elim _ _) 1 le_rfl (fun i => i.elim0)
  rw [one_pow, Real.sqrt_one, mul_one] at h
  rw [Subsingleton.elim x 1] at h ⊢
  rw [mul_inv_cancel_right₀ hqN]
  exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
end

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

private theorem tens_sum_left {K : Type} [Field K] [NumberField K] {n : ℕ} (hn : 0 < n) {ι : Type} (s : Finset ι)
    (f : ι → TI K n) (e : TF K n) : tens (∑ i ∈ s, f i) e = ∑ i ∈ s, tens (f i) e := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := ((UpperTheory.ConvolutionTheory.Tf.tensApply K n hn 0 e).2.2.2.2 (0 : ℂ)).1
    simpa using h
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, (UpperTheory.ConvolutionTheory.Tf.tensApply K n hn (f i) e).2.2.1, ih]

theorem UpperTheory.ConvolutionTheory.C.smoothDecay :
    UpperTheory.ConvolutionTheory.C.SmoothDecay := by
  intro K _ _ n μ _ a ha
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact UpperTheory.cuspDecay_of_rank_zero K μ a
  obtain ⟨U, hU, m, F, e, hF, he, rfl⟩ := UpperTheory.exists_sum_tens_of_isLeftSmooth K n hn a ha
  refine UpperTheory.cuspDecay_finset_sum K n μ (Fin m) _ fun j => ?_
  let ν : Measure (archGroup K n) := Measure.haar
  obtain ⟨ι, _, κ, γ, hκ, hFj⟩ := UpperTheory.exists_sum_conv_real_smoothT K n ν (F j) (hF j)
  rw [hFj, tens_sum_left hn Finset.univ (fun i => conv ν (κ i) (γ i)) (e j)]
  exact UpperTheory.cuspDecay_finset_sum K n μ ι _ fun i =>
    UpperTheory.cuspDecay_tens_conv_real_smoothT K n hn μ ν (κ i) (γ i) (e j) U hU (hκ i).1 (hκ i).2 (he j)
