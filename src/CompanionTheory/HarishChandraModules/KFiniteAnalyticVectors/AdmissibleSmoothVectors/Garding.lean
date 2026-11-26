module

public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.MapStdPoly
public import GroundTheory.AutomorphicForms.GKModules.ParametricIntegral

@[expose] public section

section -- merged from CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.GardingBump
open Matrix Topology Set Filter
open scoped ContDiff

noncomputable section

namespace CompanionTheory.D.gk.admitted.Gard

open PI.UpqRep

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem contDiff_entry (i j : Fin n) : ContDiff ℝ ∞ fun y : Matrix (Fin n) (Fin n) ℂ => y i j :=
  contDiff_apply_apply ℝ i j

theorem contDiff_hs : ContDiff ℝ ∞ (hs : Matrix (Fin n) (Fin n) ℂ → ℝ) := by
  unfold hs
  exact ContDiff.sum fun i _ => ContDiff.sum fun j _ => (contDiff_entry i j).norm_sq ℝ

theorem contDiff_mul :
    ContDiff ℝ ∞ fun p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ => p.1 * p.2 := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  simp only [Matrix.mul_apply]
  exact ContDiff.sum fun k _ => ((contDiff_entry i k).comp contDiff_fst).mul ((contDiff_entry k j).comp contDiff_snd)

theorem hs_eq_trace (y : Matrix (Fin n) (Fin n) ℂ) : (hs y : ℂ) = (y * yᴴ).trace := by
  simp only [hs, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

theorem hs_conj {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (y : Matrix (Fin n) (Fin n) ℂ) : hs (kᴴ * y * k) = hs y := by
  have h1 : k * kᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hk
  apply Complex.ofReal_injective
  rw [hs_eq_trace, hs_eq_trace]
  have : kᴴ * y * k * (kᴴ * y * k)ᴴ = kᴴ * (y * yᴴ * k) := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc k kᴴ, h1, Matrix.one_mul]
  rw [this, Matrix.trace_mul_comm, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem norm_le_of_hs {y : Matrix (Fin n) (Fin n) ℂ} {r : ℝ} (hr : 0 ≤ r) (h : hs y ≤ r ^ 2) : ‖y‖ ≤ r := by
  rw [Matrix.norm_le_iff hr]
  intro i j
  have h1 : ‖y i j‖ ^ 2 ≤ ∑ j, ‖y i j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖y i j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
  have h2 : ∑ j, ‖y i j‖ ^ 2 ≤ hs y :=
    Finset.single_le_sum (f := fun i => ∑ j, ‖y i j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hr two_ne_zero).1 (h1.trans (h2.trans h))

theorem exists_bump {W : Set (Matrix (Fin n) (Fin n) ℂ)} (hW : W ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ)) :
    ∃ (f : Matrix (Fin n) (Fin n) ℂ → ℝ) (S : Set (Matrix (Fin n) (Fin n) ℂ)), ContDiff ℝ ∞ f ∧ 0 ≤ f ∧ f 1 ≠ 0 ∧
      IsCompact S ∧ S ⊆ W ∧ (∀ y, f y ≠ 0 → y ∈ S) ∧
      ∀ k ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ y, f (kᴴ * y * k) = f y := by
  obtain ⟨r, hr, hrW⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hW
  refine ⟨fun y => expNegInvGlue (r ^ 2 - hs (y - 1)), Metric.closedBall 1 r, ?_, fun y => expNegInvGlue.nonneg _,
    ?_, isCompact_closedBall _ _, hrW, fun y hy => ?_, fun k hk y => ?_⟩
  · exact expNegInvGlue.contDiff.comp (contDiff_const.sub (contDiff_hs.comp (contDiff_id.sub contDiff_const)))
  · refine (expNegInvGlue.pos_of_pos ?_).ne'
    simp only [sub_self, hs, Matrix.zero_apply, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero, sub_zero]
    positivity
  · rw [mem_closedBall_iff_norm]
    refine norm_le_of_hs hr.le ?_
    by_contra h
    exact hy (expNegInvGlue.zero_of_nonpos (by linarith))
  · have h1 : kᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk
    have : kᴴ * y * k - 1 = kᴴ * (y - 1) * k := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1]
    simp only [this, hs_conj hk]

theorem isCompact_mul_inv {A S : Set (Matrix (Fin n) (Fin n) ℂ)} (hA : IsCompact A) (hS : IsCompact S)
    (hd : ∀ B ∈ S, B.det ≠ 0) :
    IsCompact ((fun p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ => p.1 * p.2⁻¹) '' (A ×ˢ S)) := by
  refine (hA.prod hS).image_of_continuousOn fun p hp => ?_
  have h1 : ContinuousAt (Inv.inv : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) p.2 := by
    refine continuousAt_matrix_inv _ ?_
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (hd _ hp.2)
  exact (continuousAt_fst.mul (h1.comp continuousAt_snd)).continuousWithinAt

end CompanionTheory.D.gk.admitted.Gard
end
end

section -- merged from CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.GardingAvg
open MeasureTheory Topology Set Filter
open scoped ContDiff

noncomputable section

namespace CompanionTheory.D.gk.admitted.Gard

section Param

variable {P Q E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem continuous_iter_partial (Φ : P × Q → E) (hΦ : ContDiff ℝ ∞ Φ) (k : ℕ) :
    Continuous fun p : P × Q => iteratedFDeriv ℝ k (fun y => Φ (y, p.2)) p.1 := by
  have h : (fun p : P × Q => iteratedFDeriv ℝ k (fun y => Φ (y, p.2)) p.1) =
      fun p => (iteratedFDeriv ℝ k Φ p).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inl ℝ P Q) := by
    funext p
    have e : (fun y => Φ (y, p.2)) =
        (fun z => Φ (z + (0, p.2))) ∘ (ContinuousLinearMap.inl ℝ P Q) := by
      funext y; simp
    have hs : ContDiff ℝ ∞ (fun z : P × Q => Φ (z + (0, p.2))) :=
      hΦ.comp (contDiff_id.add contDiff_const)
    rw [e, ContinuousLinearMap.iteratedFDeriv_comp_right _ hs _ (by exact_mod_cast le_top),
      iteratedFDeriv_comp_add_right]
    simp
  rw [h]
  exact (ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ : Fin k => ContinuousLinearMap.inl ℝ P Q)).continuous.comp
      (hΦ.continuous_iteratedFDeriv (by exact_mod_cast le_top))

end Param

section Avg

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem integrable_w (ρ : G → H →L[ℂ] H) (hρ : ∀ u, Continuous fun x => ρ x u) {w : G → ℝ}
    (hw : Continuous w) (hc : HasCompactSupport w) (u : H) : Integrable (fun x => w x • ρ x u) μ :=
  (hw.smul (hρ u)).integrable_of_hasCompactSupport hc.smul_right

theorem exists_strictHenselian_absolutely_closed_local_ring (ρ : G → H →L[ℂ] H) (hρ : ∀ u, Continuous fun x => ρ x u) (hiso : ∀ x u, ‖ρ x u‖ = ‖u‖)
    {w : G → ℝ} (hw : Continuous w) (hc : HasCompactSupport w) :
    ∃ T : H →L[ℂ] H, ∀ u, T u = ∫ x, w x • ρ x u ∂μ := by
  let L : H →ₗ[ℂ] H :=
    { toFun := fun u => ∫ x, w x • ρ x u ∂μ
      map_add' := fun u v => by
        simp only [map_add (f := _), smul_add]
        exact integral_add (integrable_w μ ρ hρ hw hc u) (integrable_w μ ρ hρ hw hc v)
      map_smul' := fun c u => by
        simp only [map_smul, RingHom.id_apply]
        rw [← integral_smul]
        simp only [smul_comm c] }
  refine ⟨L.mkContinuous (∫ x, ‖w x‖ ∂μ) fun u => ?_, fun u => rfl⟩
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  simp only [norm_smul, hiso]
  exact integral_mul_const _ _

theorem integral_mul_right_of_conj {w : G → ℝ} (hw : Continuous w) (hc : HasCompactSupport w) (h0 : 0 ≤ w)
    (h1 : w 1 ≠ 0) (k : G) (hk : ∀ x, w (k⁻¹ * x * k) = w x) (F : G → H) :
    ∫ x, F (x * k) ∂μ = ∫ x, F x ∂μ := by
  have hm := Measure.map_right_mul_eq_modularCharacterFun_smul μ k
  have hemb : MeasurableEmbedding fun x : G => x * k := (MeasurableEquiv.mulRight k).measurableEmbedding
  have hpos := hw.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := μ) hc h0 h1
  have e1 : ∫ x, w (x * k) ∂μ = ∫ x, w x ∂μ := by
    rw [← integral_mul_left_eq_self (fun x => w (x * k)) k⁻¹]
    simp only [hk]
  rw [← hemb.integral_map, hm, integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul] at e1
  have e2 : Measure.modularCharacterFun k = 1 := by
    have : ((Measure.modularCharacterFun k : NNReal) : ℝ) = 1 := by
      apply mul_right_cancel₀ hpos.ne'
      rw [e1, one_mul]
    exact_mod_cast this
  rw [← hemb.integral_map, hm, e2, one_smul]

theorem apply_alt (ρ : G → H →L[ℂ] H) (hρ : ∀ u, Continuous fun x => ρ x u)
    (hmul : ∀ x y u, ρ (x * y) u = ρ x (ρ y u)) {w : G → ℝ} (hw : Continuous w) (hc : HasCompactSupport w)
    (g : G) (u : H) :
    ρ g (∫ x, w x • ρ x u ∂μ) = ∫ x, w (g⁻¹ * x) • ρ x u ∂μ := by
  rw [← (ρ g).integral_comp_comm (integrable_w μ ρ hρ hw hc u),
    ← integral_mul_left_eq_self (fun x => w (g⁻¹ * x) • ρ x u) g]
  congr 1
  funext x
  rw [inv_mul_cancel_left, hmul, ContinuousLinearMap.map_smul_of_tower]

theorem T_comm (ρ : G → H →L[ℂ] H) (hρ : ∀ u, Continuous fun x => ρ x u)
    (hmul : ∀ x y u, ρ (x * y) u = ρ x (ρ y u)) {w : G → ℝ} (hw : Continuous w) (hc : HasCompactSupport w)
    (h0 : 0 ≤ w) (h1 : w 1 ≠ 0) (k : G) (hk : ∀ x, w (k⁻¹ * x * k) = w x) (u : H) :
    ∫ x, w x • ρ x (ρ k u) ∂μ = ρ k (∫ x, w x • ρ x u ∂μ) := by
  rw [apply_alt μ ρ hρ hmul hw hc,
    ← integral_mul_right_of_conj μ hw hc h0 h1 k hk (fun x => w (k⁻¹ * x) • ρ x u)]
  congr 1
  funext x
  rw [← mul_assoc, hk, hmul]

theorem exists_nhds_close (ρ : G → H →L[ℂ] H) (hρ : ∀ u, Continuous fun x => ρ x u) (h1 : ∀ u, ρ 1 u = u)
    (Y : Submodule ℂ H) [FiniteDimensional ℂ Y] :
    ∃ V ∈ 𝓝 (1 : G), ∀ x ∈ V, ∀ y ∈ Y, ‖ρ x y - y‖ ≤ 1 / 2 * ‖y‖ := by
  let A : G → (Y →L[ℂ] H) := fun x => (ρ x).comp Y.subtypeL - Y.subtypeL
  have hA : Continuous A := by
    rw [continuous_clm_apply]
    intro y
    exact (hρ y).sub continuous_const
  have hA1 : A 1 = 0 := by
    ext y
    simp [A, h1]
  refine ⟨{x | ‖A x‖ < 1 / 2}, ?_, fun x hx y hy => ?_⟩
  · exact (isOpen_lt hA.norm continuous_const).mem_nhds (by simp [hA1])
  · have := (A x).le_opNorm ⟨y, hy⟩
    exact this.trans (mul_le_mul_of_nonneg_right (le_of_lt hx) (norm_nonneg _))

theorem eq_zero_of_alt_alt (ρ : G → H →L[ℂ] H) (hρ : ∀ u, Continuous fun x => ρ x u)
    {w : G → ℝ} (hw : Continuous w) (hc : HasCompactSupport w) (h0 : 0 ≤ w) (h1 : w 1 ≠ 0)
    (y : H) (hy : ∀ x, w x ≠ 0 → ‖ρ x y - y‖ ≤ 1 / 2 * ‖y‖) (hT : ∫ x, w x • ρ x y ∂μ = 0) : y = 0 := by
  have hpos := hw.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := μ) hc h0 h1
  have hwi : Integrable w μ := hw.integrable_of_hasCompactSupport hc
  have e : ∫ x, w x • (ρ x y - y) ∂μ = -((∫ x, w x ∂μ) • y) := by
    simp only [smul_sub]
    rw [integral_sub (integrable_w μ ρ hρ hw hc y) (hwi.smul_const y), hT, integral_smul_const, zero_sub]
  have b : ‖∫ x, w x • (ρ x y - y) ∂μ‖ ≤ ∫ x, w x * (1 / 2 * ‖y‖) ∂μ := by
    refine norm_integral_le_of_norm_le (hwi.mul_const _) (Eventually.of_forall fun x => ?_)
    rw [norm_smul, Real.norm_of_nonneg (h0 x)]
    by_cases hx : w x = 0
    · simp [hx]
    · exact mul_le_mul_of_nonneg_left (hy x hx) (h0 x)
  rw [e, norm_neg, norm_smul, Real.norm_of_nonneg hpos.le, integral_mul_const] at b
  have := le_of_mul_le_mul_left b hpos
  have h2 : ‖y‖ = 0 := by linarith [norm_nonneg y]
  exact norm_eq_zero.1 h2

end Avg

theorem exists_preimage {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] (Y : Submodule ℂ H)
    [FiniteDimensional ℂ Y] (T : H →L[ℂ] H) (hT : ∀ y ∈ Y, T y ∈ Y) (hi : ∀ y ∈ Y, T y = 0 → y = 0) :
    ∀ v ∈ Y, ∃ u, T u = v := by
  intro v hv
  let L : Y →ₗ[ℂ] Y := (T : H →ₗ[ℂ] H).restrict hT
  have hL : Function.Injective L := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    exact Subtype.ext (hi y y.2 (congrArg Subtype.val hy))
  obtain ⟨u, hu⟩ := LinearMap.surjective_of_injective hL ⟨v, hv⟩
  exact ⟨u, congrArg Subtype.val hu⟩

end CompanionTheory.D.gk.admitted.Gard
end
end

open MeasureTheory Matrix Topology Set Filter
open scoped ContDiff

noncomputable section

namespace CompanionTheory.D.gk.admitted

open PI.UpqRep

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Gard

theorem contDiff_integral_comp {P Q E α : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace α] [T2Space α] [SecondCountableTopology α] [MeasurableSpace α] [OpensMeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasureOnCompacts μ] (Φ : P × Q → E) (hΦ : ContDiff ℝ ∞ Φ) (q : α → Q)
    (hq : Continuous q)
    (hsupp : ∀ y₀ : P, ∃ U ∈ 𝓝 y₀, ∃ C : Set α, IsCompact C ∧ ∀ y ∈ U, ∀ a ∉ C, Φ (y, q a) = 0) :
    ContDiff ℝ ∞ fun y => ∫ a, Φ (y, q a) ∂μ := by
  refine GroundTheory.Automorphic.contDiff_integral_of_iteratedFDeriv (μ := μ) (fun y a => Φ (y, q a))
    (fun a => hΦ.comp (contDiff_id.prodMk contDiff_const)) (fun k => ?_) hsupp
  have h : Continuous fun p : P × α => (p.1, q p.2) := continuous_fst.prodMk (hq.comp continuous_snd)
  exact (continuous_iter_partial Φ hΦ k).comp h

variable {n : ℕ} {ε : Fin n → Bool}

theorem toM_mul (x y : UJ ε) : toM (x * y) = toM x * toM y := rfl

theorem toM_one : toM (1 : UJ ε) = 1 := rfl

theorem emb_toM : IsClosedEmbedding (toM : UJ ε → Matrix (Fin n) (Fin n) ℂ) := (isClosedEmbeddingMatrix n ε).1

theorem toM_mem (x : UJ ε) : toM x ∈ UJset ε := x.2

theorem exists_toM {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : ∃ x : UJ ε, toM x = g := by
  have : g ∈ Set.range (coeMatrixAlt ε) := by rw [range_coeMatrix]; exact hg
  exact this

theorem inUJ_of_mem_Kset {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) : inUJ ε k := by
  have h1 : kᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk.1
  unfold inUJ
  rw [Matrix.mul_assoc, ← hk.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem toM_inv_of_unitary {k : UJ ε} (hk : toM k ∈ Matrix.unitaryGroup (Fin n) ℂ) : toM k⁻¹ = (toM k)ᴴ :=
  Units.inv_eq_of_mul_eq_one_right (Matrix.mem_unitaryGroup_iff.1 hk)

theorem contDiff_Phi {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {f : Matrix (Fin n) (Fin n) ℂ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ fun p : Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ × H) => f (p.2.1 * p.1) • p.2.2 := by
  have h1 : ContDiff ℝ ∞ fun p : Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ × H) => (p.2.1, p.1) :=
    contDiff_snd.fst.prodMk contDiff_fst
  have h2 : ContDiff ℝ ∞ fun p : Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ × H) => p.2.1 * p.1 := by
    have := contDiff_mul.comp h1
    simpa only [Function.comp_def] using this
  have h3 : ContDiff ℝ ∞ fun p : Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ × H) => f (p.2.1 * p.1) :=
    hf.comp h2
  exact h3.smul contDiff_snd.snd

theorem supp_local {f : Matrix (Fin n) (Fin n) ℂ → ℝ} {S : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hS : IsCompact S) (hd : ∀ B ∈ S, B.det ≠ 0) (hfS : ∀ y, f y ≠ 0 → y ∈ S) (g₀ : Matrix (Fin n) (Fin n) ℂ) :
    ∃ U ∈ 𝓝 g₀, ∃ C : Set (UJ ε), IsCompact C ∧ ∀ g ∈ U, ∀ x ∉ C, f (toM x⁻¹ * g) = 0 := by
  refine ⟨Metric.closedBall g₀ 1, Metric.closedBall_mem_nhds _ one_pos, _,
    emb_toM.isCompact_preimage (isCompact_mul_inv (isCompact_closedBall g₀ 1) hS hd), fun g hg x hx => ?_⟩
  by_contra h
  have hB := hfS _ h
  refine hx ⟨(g, toM x⁻¹ * g), ⟨hg, hB⟩, ?_⟩
  have hu : IsUnit (toM x⁻¹ * g).det := isUnit_iff_ne_zero.2 (hd _ hB)
  have e : g = toM x * (toM x⁻¹ * g) := by
    rw [← Matrix.mul_assoc, ← toM_mul, mul_inv_cancel, toM_one, Matrix.one_mul]
  show g * (toM x⁻¹ * g)⁻¹ = toM x
  calc g * (toM x⁻¹ * g)⁻¹ = toM x * (toM x⁻¹ * g) * (toM x⁻¹ * g)⁻¹ := by rw [← e]
    _ = toM x := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]

theorem contDiff_avg {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (v : UJ ε → H) (hv : Continuous v) {f : Matrix (Fin n) (Fin n) ℂ → ℝ} {S : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hf : ContDiff ℝ ∞ f) (hS : IsCompact S) (hd : ∀ B ∈ S, B.det ≠ 0) (hfS : ∀ y, f y ≠ 0 → y ∈ S) :
    ContDiff ℝ ∞ fun g : Matrix (Fin n) (Fin n) ℂ => ∫ x : UJ ε, f (toM x⁻¹ * g) • v x ∂(muG ε) := by
  have hq : Continuous fun x : UJ ε => (toM x⁻¹, v x) := (emb_toM.continuous.comp continuous_inv).prodMk hv
  have key := contDiff_integral_comp (muG ε) _ (contDiff_Phi (H := H) hf) _ hq fun g₀ => by
    obtain ⟨U, hU, C, hC, h⟩ := supp_local (ε := ε) hS hd hfS g₀
    refine ⟨U, hU, C, hC, fun g hg x hx => ?_⟩
    simp only [h g hg x hx, zero_smul]
  simpa only using key

end Gard


open Gard in
theorem garding_finite_smooth_vectors : GardingFin := by
  open scoped Pointwise in
  intro n ε H _ _ _ σ hσ Y _ hY v hv
  obtain ⟨⟨h1, hm⟩, hiso, hcont⟩ := hσ
  let ρ : UJ ε → H →L[ℂ] H := fun x => σ (toM x)
  have hρ : ∀ u, Continuous fun x => ρ x u := fun u =>
    (hcont u).comp_continuous emb_toM.continuous toM_mem
  have hmul : ∀ x y u, ρ (x * y) u = ρ x (ρ y u) := fun x y u => by
    simp only [ρ, toM_mul, hm _ (toM_mem x) _ (toM_mem y), ContinuousLinearMap.comp_apply]
  have hρ1 : ∀ u, ρ 1 u = u := fun u => by simp only [ρ, toM_one, h1, one_apply_eq_self]
  obtain ⟨V, hV, hclose⟩ := exists_nhds_close ρ hρ hρ1 Y
  have hVi : V⁻¹ ∈ 𝓝 (1 : UJ ε) := inv_mem_nhds_one _ hV
  rw [emb_toM.isInducing.nhds_eq_comap, mem_comap] at hVi
  obtain ⟨W, hW, hWV⟩ := hVi
  have hD : {y : Matrix (Fin n) (Fin n) ℂ | y.det ≠ 0} ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ) :=
    (isOpen_ne_fun continuous_id.matrix_det continuous_const).mem_nhds (by simp)
  obtain ⟨f, S, hf, hf0, hf1, hS, hSW, hfS, hfk⟩ := exists_bump (inter_mem hW hD)
  let w : UJ ε → ℝ := fun x => f (toM x⁻¹)
  have hw : Continuous w := hf.continuous.comp (emb_toM.continuous.comp continuous_inv)
  have hc : HasCompactSupport w := by
    refine HasCompactSupport.intro (emb_toM.isCompact_preimage hS).inv fun x hx => ?_
    by_contra h
    exact hx (hfS _ h)
  have h0 : 0 ≤ w := fun x => hf0 _
  have hw1 : w 1 ≠ 0 := by simpa only [w, inv_one, toM_one] using hf1
  obtain ⟨T, hT⟩ := exists_strictHenselian_absolutely_closed_local_ring (muG ε) ρ hρ (fun x u => hiso _ (toM_mem x) u) hw hc
  have hTK : ∀ k ∈ Kset ε, ∀ u, T (σ k u) = σ k (T u) := by
    intro k hk u
    obtain ⟨k', rfl⟩ := exists_toM (inUJ_of_mem_Kset hk)
    rw [hT, hT]
    refine T_comm (muG ε) ρ hρ hmul hw hc h0 hw1 k' (fun x => ?_) u
    simp only [w, _root_.mul_inv_rev, inv_inv]
    rw [← mul_assoc, toM_mul, toM_mul, toM_inv_of_unitary hk.1, hfk _ hk.1]
  have hinj : ∀ y ∈ Y, T y = 0 → y = 0 := by
    intro y hy hTy
    rw [hT] at hTy
    refine eq_zero_of_alt_alt (muG ε) ρ hρ hw hc h0 hw1 y (fun x hx => hclose x ?_ y hy) hTy
    have : x⁻¹ ∈ V⁻¹ := hWV (hSW (hfS _ hx)).1
    simpa using this
  obtain ⟨u, rfl⟩ := exists_preimage Y T (hY T hTK) hinj v hv
  intro g₀ _
  refine ⟨univ, fun g => ∫ x : UJ ε, f (toM x⁻¹ * g) • ρ x u ∂(muG ε), isOpen_univ, mem_univ _,
    (contDiff_avg (fun x => ρ x u) (hρ u) hf hS (fun B hB => (hSW hB).2) hfS).contDiffOn, fun g _ hg => ?_⟩
  obtain ⟨g', rfl⟩ := exists_toM (ε := ε) hg
  show ρ g' (T u) = _
  rw [hT, apply_alt (muG ε) ρ hρ hmul hw hc]
  simp only [w, _root_.mul_inv_rev, inv_inv, toM_mul]

end CompanionTheory.D.gk.admitted
