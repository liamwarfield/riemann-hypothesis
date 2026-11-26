module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.HermRealSmul

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.IILeft
noncomputable section

open MeasureTheory Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.II

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def cE (E : M2 n) (s : ℝ) : M2 n := NormedSpace.exp (s • E)

set_option backward.isDefEq.respectTransparency false in
theorem cE_entry (E : M2 n) (a b : Fin n ⊕ Fin n) :
    HasDerivAt (fun s : ℝ => cE E s a b) (E a b) 0 := by
  open scoped Matrix.Norms.Operator in
  have h1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) E (0 : ℝ)
  open scoped Matrix.Norms.Operator in
  have h2 := (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ a b)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  simpa [Function.comp_def, cE] using h2

theorem cE_hasDerivAt0 (E : M2 n) : HasDerivAt (cE E) E 0 := by
  have h : HasDerivAt (fun s : ℝ => (cE E s : (Fin n ⊕ Fin n) → (Fin n ⊕ Fin n) → ℂ))
      (E : (Fin n ⊕ Fin n) → (Fin n ⊕ Fin n) → ℂ) 0 :=
    hasDerivAt_pi.2 fun a => hasDerivAt_pi.2 fun b => cE_entry E a b
  exact h

theorem cE_zero (E : M2 n) : cE E 0 = 1 := by simp [cE]

theorem cE_add (E : M2 n) (s t : ℝ) : cE E (s + t) = cE E s * cE E t := by
  unfold cE
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ ((Commute.refl E).smul_left s |>.smul_right t)

def mulL (A : M2 n) : M2 n →L[ℝ] M2 n := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ A)

def mulR (A : M2 n) : M2 n →L[ℝ] M2 n := LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ A)

theorem mulL_apply (A B : M2 n) : mulL A B = A * B := rfl

theorem cE_hasDerivAt (E : M2 n) (s : ℝ) : HasDerivAt (cE E) (cE E s * E) s := by
  have h0 : HasDerivAt (fun t : ℝ => cE E (t - s)) E s := by
    have h : HasDerivAt (cE E) E (s - s) := by simpa using cE_hasDerivAt0 E
    exact HasDerivAt.comp_sub_const s s h
  have h1 : HasDerivAt (fun t : ℝ => cE E s * cE E (t - s)) (cE E s * E) s :=
    (mulL (cE E s)).hasFDerivAt.comp_hasDerivAt s h0
  refine h1.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  simp only
  rw [← cE_add]
  congr 1
  ring

theorem cE_continuous (E : M2 n) : Continuous (cE E) :=
  continuous_iff_continuousAt.2 fun s => (cE_hasDerivAt E s).continuousAt

theorem JJ_conjTranspose : (JJ n)ᴴ = -JJ n := by
  simp [JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_neg]

theorem cE_inK (E : M2 n) (hE : Eᴴ = -E) (hEJ : E * JJ n = JJ n * E) (s : ℝ) : InK (cE E s) := by
  have hct : (cE E s)ᴴ = cE E (-s) := by
    unfold cE
    rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hE]
    simp [neg_smul, smul_neg]
  have hinv : (cE E s)ᴴ * cE E s = 1 := by
    rw [hct, ← cE_add, neg_add_cancel, cE_zero]
  have hcomm : cE E s * JJ n = JJ n * cE E s := by
    have hc : Commute (s • E) (JJ n) := by
      show s • E * JJ n = JJ n * (s • E)
      rw [Matrix.smul_mul, hEJ, Matrix.mul_smul]
    exact (hc.exp_left).eq
  refine ⟨?_, hinv⟩
  unfold InG
  rw [Matrix.mul_assoc, ← hcomm, ← Matrix.mul_assoc, hinv, Matrix.one_mul]

theorem core {Kg : Type} [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg]
    [MeasurableSpace Kg] [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n)
    (hι : Continuous ι) (hK : ∀ g, InK g ↔ ∃ k, ι k = g)
    (F : M2 n → ℂ) (U : Set (M2 n)) (hU : IsOpen U) (hKU : KSet n ⊆ U) (hF : ContDiffOn ℝ 1 F U)
    (E : M2 n) (hE : Eᴴ = -E) (hEJ : E * JJ n = JJ n * E) :
    Integrable (fun k => fderiv ℝ F (ι k) (E * ι k)) μ ∧ ∫ k, fderiv ℝ F (ι k) (E * ι k) ∂μ = 0 := by
  have hΦc : Continuous (fun p : ℝ × Kg => cE E p.1 * ι p.2) :=
    ((cE_continuous E).comp continuous_fst).matrix_mul (hι.comp continuous_snd)
  have hmem0 : ∀ k, ι k ∈ U := fun k => hKU ((hK (ι k)).2 ⟨k, rfl⟩)
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ k ∈ (Set.univ : Set Kg), cE E s * ι k ∈ U := by
    refine isCompact_univ.eventually_forall_of_forall_eventually fun k _ => ?_
    have h0 : cE E 0 * ι k ∈ U := by rw [cE_zero, Matrix.one_mul]; exact hmem0 k
    exact hΦc.continuousAt.preimage_mem_nhds (hU.mem_nhds h0)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hin : ∀ s : ℝ, |s| ≤ ε / 2 → ∀ k, cE E s * ι k ∈ U := fun s hs k =>
    hball (by rw [Real.dist_eq, sub_zero]; linarith) k (Set.mem_univ _)
  have hfd : ContinuousOn (fderiv ℝ F) U := hF.continuousOn_fderiv_of_isOpen hU le_rfl
  set S : Set (ℝ × Kg) := Set.Icc (-(ε / 2)) (ε / 2) ×ˢ Set.univ
  have hS : IsCompact S := isCompact_Icc.prod isCompact_univ
  have hmapS : ∀ p ∈ S, cE E p.1 * ι p.2 ∈ U := fun p hp =>
    hin p.1 (abs_le.2 ⟨hp.1.1, hp.1.2⟩) p.2
  have hGc : ContinuousOn (fun p : ℝ × Kg => fderiv ℝ F (cE E p.1 * ι p.2) (cE E p.1 * E * ι p.2)) S := by
    refine ContinuousOn.clm_apply (hfd.comp hΦc.continuousOn hmapS) ?_
    exact ((((cE_continuous E).comp continuous_fst).matrix_mul continuous_const).matrix_mul (hι.comp continuous_snd)).continuousOn
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hGc
  have hdiffF : ∀ y ∈ U, DifferentiableAt ℝ F y := fun y hy =>
    (hF.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hy)
  have hs : Metric.ball (0 : ℝ) (ε / 2) ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds _ (by linarith)
  have hsub : ∀ s ∈ Metric.ball (0 : ℝ) (ε / 2), |s| ≤ ε / 2 := fun s hs' => by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hs'; exact hs'.le
  have hcontF : ∀ s : ℝ, |s| ≤ ε / 2 → Continuous (fun k => F (cE E s * ι k)) := fun s hs' =>
    hF.continuousOn.comp_continuous (continuous_const.matrix_mul hι) fun k => hin s hs' k
  have hcontF' : ∀ s : ℝ, |s| ≤ ε / 2 →
      Continuous (fun k => fderiv ℝ F (cE E s * ι k) (cE E s * E * ι k)) := fun s hs' =>
    (hfd.comp_continuous (continuous_const.matrix_mul hι) fun k => hin s hs' k).clm_apply (continuous_const.matrix_mul hι)
  have h0 : |(0 : ℝ)| ≤ ε / 2 := by rw [abs_zero]; linarith
  have hint0 : Integrable (fun k => F (cE E 0 * ι k)) μ := by
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn (hcontF 0 h0).continuousOn
    exact Integrable.mono' (integrable_const C) (hcontF 0 h0).aestronglyMeasurable
      (Eventually.of_forall fun k => hC k (Set.mem_univ _))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := (0 : ℝ))
    (F := fun s k => F (cE E s * ι k)) (bound := fun _ => B)
    (F' := fun s k => fderiv ℝ F (cE E s * ι k) (cE E s * E * ι k)) hs
    (by filter_upwards [hs] with s hs' using (hcontF s (hsub s hs')).aestronglyMeasurable)
    hint0 (hcontF' 0 h0).aestronglyMeasurable
    (Eventually.of_forall fun k s hs' => hB (s, k) ⟨⟨(abs_le.1 (hsub s hs')).1, (abs_le.1 (hsub s hs')).2⟩, Set.mem_univ _⟩)
    (integrable_const B)
    (Eventually.of_forall fun k s hs' => by
      have h1 := cE_hasDerivAt E s
      have h2 : HasDerivAt (fun t => cE E t * ι k) (cE E s * E * ι k) s :=
        (mulR (ι k)).hasFDerivAt.comp_hasDerivAt s h1
      exact (hdiffF _ (hin s (hsub s hs') k)).hasFDerivAt.comp_hasDerivAt s h2)
  have hconst : (fun s : ℝ => ∫ k, F (cE E s * ι k) ∂μ) = fun _ => ∫ k, F (ι k) ∂μ := by
    funext s
    obtain ⟨κ, hκ⟩ := (hK (cE E s)).1 (cE_inK E hE hEJ s)
    have : (fun k => F (cE E s * ι k)) = fun k => (fun k' => F (ι k')) (κ * k) := by
      funext k; show F (cE E s * ι k) = F (ι (κ * k)); rw [map_mul, hκ]
    rw [this, integral_mul_left_eq_self (fun k' => F (ι k')) κ]
  have hd0 : HasDerivAt (fun s : ℝ => ∫ k, F (cE E s * ι k) ∂μ) 0 0 := by
    rw [hconst]; exact hasDerivAt_const _ _
  have huniq := key.2.unique hd0
  have hF' : (fun k => fderiv ℝ F (cE E 0 * ι k) (cE E 0 * E * ι k)) = fun k => fderiv ℝ F (ι k) (E * ι k) := by
    funext k; simp [cE_zero]
  rw [hF'] at key huniq
  exact ⟨key.1, huniq⟩

theorem reK_skew (e : M2 n) : (reK e)ᴴ = -reK e := by
  ext i j
  simp only [reK, conjTranspose_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.neg_apply, smul_eq_mul]
  apply Complex.ext <;> simp <;> ring

theorem imK_skew (e : M2 n) : (imK e)ᴴ = -imK e := by
  ext i j
  simp only [imK, conjTranspose_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.neg_apply, smul_eq_mul]
  apply Complex.ext <;> simp <;> ring

theorem comm_conjT {e : M2 n} (he : e * JJ n = JJ n * e) : eᴴ * JJ n = JJ n * eᴴ := by
  have h := congrArg conjTranspose he
  rw [conjTranspose_mul, conjTranspose_mul, JJ_conjTranspose] at h
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_inj] at h
  exact h.symm

theorem reK_comm {e : M2 n} (he : e * JJ n = JJ n * e) : reK e * JJ n = JJ n * reK e := by
  unfold reK
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, he, comm_conjT he]

theorem imK_comm {e : M2 n} (he : e * JJ n = JJ n * e) : imK e * JJ n = JJ n * imK e := by
  unfold imK
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, he, comm_conjT he]

theorem leftDeriv : LeftDeriv := by
  intro n Kg _ _ _ _ _ _ μ _ ι hι hK F U hU hKU hF e he
  obtain ⟨i1, z1⟩ := core μ ι hι hK F U hU hKU hF (reK e) (reK_skew e) (reK_comm he)
  obtain ⟨i2, z2⟩ := core μ ι hι hK F U hU hKU hF (imK e) (imK_skew e) (imK_comm he)
  refine ⟨i1.add (i2.const_mul Complex.I), ?_⟩
  unfold dK
  rw [integral_add i1 (i2.const_mul _), integral_const_mul, z1, z2]
  simp

end PositivityTheory.Rg.Sw.LVs.II
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.CayleyG
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem analyticAt_det {ι : Type} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) :
    AnalyticAt ℂ (fun T : Matrix ι ι ℂ => T.det) X := by
  have he : ∀ a b : ι, AnalyticAt ℂ (fun T : Matrix ι ι ℂ => T a b) X := fun a b =>
    ((ContinuousLinearMap.proj b).comp
      (ContinuousLinearMap.proj a : (ι → ι → ℂ) →L[ℂ] (ι → ℂ))).analyticAt X
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  refine Finset.analyticAt_fun_sum _ fun σ _ => ?_
  exact analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => he (σ i) i)

theorem analyticAt_det_one_add_zpow {ι : Type} [Fintype ι] [DecidableEq ι] (t : ℤ) :
    AnalyticAt ℂ (fun T : Matrix ι ι ℂ => (1 + T).det ^ t) 0 := by
  have h1 : AnalyticAt ℂ (fun T : Matrix ι ι ℂ => (1 + T).det) 0 :=
    (analyticAt_det (1 + 0)).comp (analyticAt_const.add analyticAt_id)
  exact h1.zpow (by simp)

theorem cayley_of (hE : Equivar) (hR : Reindex) (hK : KappaFin) : Cayley := by
  intro ι _ _ A t
  set e := Fintype.equivFin ι
  have h1 := hE ι (fun T : Matrix ι ι ℂ => (1 + T).det ^ t) A (analyticAt_det_one_add_zpow t)
  have h2 := hR ι (Fin (Fintype.card ι)) e
    (fun S : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ => (1 + S).det ^ t)
    (analyticAt_det_one_add_zpow t)
  have h3 : (fun T : Matrix ι ι ℂ => (1 + Matrix.reindex e e T).det ^ t) =
      fun T => (1 + T).det ^ t := by
    funext T
    have h4 : 1 + Matrix.reindex e e T = Matrix.reindex e e (1 + T) := by
      ext i j
      simp [Matrix.one_apply]
    rw [h4, Matrix.det_reindex_self]
  rw [h3, hK] at h2
  rw [h1, h2, mul_comm]

end PositivityTheory.Rg.Sw.LVs
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.AnalyticAtDet
noncomputable section

open Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.CK

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PositivityTheory.Rg.Sw.LVs

def H (N : ℕ) (t : ℤ) (T : Matrix (Fin N) (Fin N) ℂ) : ℂ := (1 + T).det ^ t

theorem analyticAt_det {ι : Type} [Fintype ι] [DecidableEq ι] (M0 : Matrix ι ι ℂ) :
    AnalyticAt ℂ (fun T : Matrix ι ι ℂ => T.det) M0 := by
  have he : ∀ a b : ι, AnalyticAt ℂ (fun T : Matrix ι ι ℂ => T a b) M0 := fun a b =>
    ((ContinuousLinearMap.proj b).comp
      (ContinuousLinearMap.proj a : (ι → ι → ℂ) →L[ℂ] (ι → ℂ))).analyticAt M0
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  refine Finset.analyticAt_fun_sum _ fun σ _ => ?_
  exact analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => he (σ i) i)

theorem analyticAt_H (N : ℕ) (t : ℤ) (T0 : Matrix (Fin N) (Fin N) ℂ) (h : (1 + T0).det ≠ 0) :
    AnalyticAt ℂ (H N t) T0 := by
  have hd : AnalyticAt ℂ (fun T : Matrix (Fin N) (Fin N) ℂ => (1 + T).det) T0 :=
    (analyticAt_det (1 + T0)).comp (analyticAt_const.add analyticAt_id)
  exact hd.zpow h

end PositivityTheory.Rg.Sw.LVs.CK
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TCMatB
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.BlkB
noncomputable def UpperTheory.Reformulated.B.Yha8.blkA :
    {n : ℕ} → ℕ → Finset (Fin n) :=
    fun {n : ℕ} (j : ℕ) ↦ {i : Fin n | (↑i : ℕ) < j}

noncomputable def UpperTheory.Reformulated.B.Yha8.blkB :
    {n : ℕ} → ℕ → Finset (Fin n) :=
    fun {n : ℕ} (j : ℕ) ↦ (UpperTheory.Reformulated.B.Yha8.blkA j)ᶜ

theorem UpperTheory.Reformulated.B.Yha8.main :
    ∀ {n : ℕ} (j : ℕ) (Q S : Matrix (Fin n) (Fin n) ℂ),
      (∀ (a b : Fin n), Q a b ≠ (0 : ℂ) → b ∈ UpperTheory.Reformulated.B.Yha8.blkA j) →
        (∀ (a b : Fin n), S a b ≠ (0 : ℂ) → a ∈ UpperTheory.Reformulated.B.Yha8.blkB j) → Q * S = (0 : Matrix (Fin n) (Fin n) ℂ) := by
  intro n j Q S hQ hS
  ext a c
  rw [Matrix.mul_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro b _
  by_cases hq : Q a b = 0
  · simp [hq]
  by_cases hs : S b c = 0
  · simp [hs]
  exfalso
  have h1 := hQ a b hq
  have h2 := hS b c hs
  unfold UpperTheory.Reformulated.B.Yha8.blkB at h2
  rw [Finset.mem_compl] at h2
  exact h2 h1
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TCMatA
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.LVs.TC

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

theorem cm_mul_cmI : Cm n * CmI n = 1 := by
  rw [Cm, CmI, Matrix.mul_smul, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_smul, fromBlocks_inj]
  simp [smul_smul]
  have h : -(Complex.I * 2⁻¹ * Complex.I + Complex.I * 2⁻¹ * Complex.I) = 1 := by
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [← neg_add, ← add_smul, ← neg_smul, h, one_smul]

theorem cmI_mul_cm : CmI n * Cm n = 1 := by
  rw [Cm, CmI, Matrix.smul_mul, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_smul, fromBlocks_inj]
  simp [smul_smul]
  have h : -(Complex.I * 2⁻¹ * Complex.I + Complex.I * 2⁻¹ * Complex.I) = 1 := by
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [← neg_add, ← add_smul, ← neg_smul, h, one_smul]

theorem cm_inv : (Cm n)⁻¹ = CmI n := Matrix.inv_eq_right_inv cm_mul_cmI

theorem cmH_JJ_cm : (Cm n)ᴴ * JJ n * Cm n = fromBlocks ((-(2 * Complex.I)) • 1) 0 0 ((2 * Complex.I) • 1) := by
  rw [Cm, JJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj]
  simp [smul_smul]
  refine ⟨?_, ?_⟩
  · rw [← neg_add, ← add_smul, two_mul]
  · rw [← add_smul, two_mul]

end PositivityTheory.Rg.Sw.LVs.TC
end
end

noncomputable section

open Matrix ComplexConjugate

namespace PositivityTheory.Rg.Sw.LVs.TC

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

theorem jj_mul_jj : JJ n * JJ n = -1 := by
  unfold JJ
  rw [fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]
  simp

theorem inG_mul {g h : M2 n} (hg : InG g) (hh : InG h) : InG (g * h) := by
  unfold InG at *
  rw [conjTranspose_mul, show hᴴ * gᴴ * JJ n * (g * h) = hᴴ * (gᴴ * JJ n * g) * h by simp only [Matrix.mul_assoc], hg, hh]

theorem inG_left_inv {g : M2 n} (hg : InG g) : (-(JJ n) * gᴴ * JJ n) * g = 1 := by
  unfold InG at hg
  rw [show -(JJ n) * gᴴ * JJ n * g = -(JJ n) * (gᴴ * JJ n * g) by simp only [Matrix.mul_assoc], hg, neg_mul, jj_mul_jj,
    neg_neg]

theorem inG_mul_inv {g : M2 n} (hg : InG g) : g * g⁻¹ = 1 := by
  rw [Matrix.inv_eq_left_inv (inG_left_inv hg)]
  exact mul_eq_one_comm.1 (inG_left_inv hg)

theorem inG_inv {g : M2 n} (hg : InG g) : InG g⁻¹ := by
  have h1 := inG_mul_inv hg
  unfold InG at *
  calc (g⁻¹)ᴴ * JJ n * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * JJ n * g) * g⁻¹ := by rw [hg]
    _ = (g * g⁻¹)ᴴ * JJ n * (g * g⁻¹) := by rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = JJ n := by rw [h1]; simp

theorem mul_compl_zero (j : ℕ) (Q S : Matrix (Fin n) (Fin n) ℂ) (hQ : ∀ a b, Q a b ≠ 0 → b ∈ blkA j)
    (hS : ∀ a b, S a b ≠ 0 → a ∈ blkB j) : Q * S = 0 :=
  _root_.UpperTheory.Reformulated.B.Yha8.main j Q S hQ hS

theorem mX_factor (j : ℕ) (P Q R S : Matrix (Fin n) (Fin n) ℂ) (hP : ∀ a b, P a b ≠ 0 → a ∈ blkA j ∧ b ∈ blkB j)
    (hS : ∀ a b, S a b ≠ 0 → a ∈ blkB j ∧ b ∈ blkA j) (hQ : ∀ a b, Q a b ≠ 0 → a ∈ blkA j ∧ b ∈ blkA j)
    (hR : ∀ a b, R a b ≠ 0 → a ∈ blkB j ∧ b ∈ blkB j) :
    mX (1 + P) Q R (1 + S) = mX 1 Q R 1 * mX (1 + P) 0 0 (1 + S) := by
  have hQS : Q * S = 0 := mul_compl_zero j Q S (fun a b h => (hQ a b h).2) (fun a b h => (hS a b h).1)
  have hRP : R * P = 0 := by
    ext a b
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hr : R a k = 0
    · simp [hr]
    by_cases hp : P k b = 0
    · simp [hp]
    exact absurd (hP k b hp).1 (by have := (hR a k hr).2; simp [blkB] at this; exact this)
  unfold mX
  rw [cm_inv, show Cm n * fromBlocks 1 Q R 1 * CmI n * (Cm n * fromBlocks (1 + P) 0 0 (1 + S) * CmI n) =
      Cm n * (fromBlocks 1 Q R 1 * (CmI n * Cm n) * fromBlocks (1 + P) 0 0 (1 + S)) * CmI n by
        simp only [Matrix.mul_assoc], cmI_mul_cm, Matrix.mul_one, fromBlocks_multiply]
  simp [Matrix.mul_add, hQS, hRP]

end PositivityTheory.Rg.Sw.LVs.TC
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.CayleyEq
noncomputable section

open Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.CEq

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
theorem iteratedFDeriv_comp_clm (F : Matrix κ κ ℂ → ℂ) (hF : AnalyticAt ℂ F 0)
    (L : Matrix ι ι ℂ →L[ℂ] Matrix κ κ ℂ) (n : ℕ) (v : Fin n → Matrix ι ι ℂ) :
    iteratedFDeriv ℂ n (F ∘ L) 0 v = iteratedFDeriv ℂ n F 0 (fun i => L (v i)) := by
  obtain ⟨s, hs0, hAs⟩ := hF.exists_mem_nhds_analyticOnNhd
  have ht : IsOpen (interior s) := isOpen_interior
  have h0t : (0 : Matrix κ κ ℂ) ∈ interior s := mem_interior_iff_mem_nhds.mpr hs0
  have hcd : ContDiffOn ℂ ω F (interior s) := (hAs.mono interior_subset).contDiffOn ht.uniqueDiffOn
  have hpre : IsOpen (L ⁻¹' interior s) := ht.preimage L.continuous
  have hL0 : L 0 ∈ interior s := by simpa using h0t
  have h0pre : (0 : Matrix ι ι ℂ) ∈ L ⁻¹' interior s := hL0
  have key := L.iteratedFDerivWithin_comp_right hcd ht.uniqueDiffOn hpre.uniqueDiffOn hL0
    (i := n) le_top
  have e1 := iteratedFDerivWithin_of_isOpen (𝕜 := ℂ) (f := F ∘ L) n hpre h0pre
  have e2 := iteratedFDerivWithin_of_isOpen (𝕜 := ℂ) (f := F) n ht h0t
  have hz : L 0 = 0 := L.map_zero
  rw [← e1, ← e2]
  erw [key]
  exact congrArg (fun y => iteratedFDerivWithin ℂ n F (interior s) y (fun i => L (v i))) hz

omit [DecidableEq κ] in
theorem symm_perm (F : Matrix κ κ ℂ → ℂ) (hF : AnalyticAt ℂ F 0) {n : ℕ} (v : Fin n → Matrix κ κ ℂ)
    (π : Equiv.Perm (Fin n)) : iteratedFDeriv ℂ n F 0 (v ∘ π) = iteratedFDeriv ℂ n F 0 v :=
  (hF.contDiffAt).iteratedFDeriv_comp_perm v π

def Dg {n : ℕ} (f : κ ≃ Fin n) (F : Matrix κ κ ℂ → ℂ) : ℂ :=
  ∑ σ : Equiv.Perm κ, (Equiv.Perm.sign σ : ℂ) *
    iteratedFDeriv ℂ n F 0 (fun i => Matrix.single (f.symm i) (σ (f.symm i)) 1)

omit [DecidableEq ι] in
theorem detD_eq_Dg (F : Matrix κ κ ℂ → ℂ) : detD F = Dg (Fintype.equivFin κ) F := rfl

theorem Dg_indep (F : Matrix κ κ ℂ → ℂ) (hF : AnalyticAt ℂ F 0) {n m : ℕ} (f : κ ≃ Fin n) (g : κ ≃ Fin m) :
    Dg f F = Dg g F := by
  have hnm : n = m := by simpa using Fintype.card_congr (f.symm.trans g)
  subst hnm
  unfold Dg
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  have hv : (fun i => Matrix.single (f.symm i) (σ (f.symm i)) (1 : ℂ)) =
      (fun i => Matrix.single (g.symm i) (σ (g.symm i)) (1 : ℂ)) ∘ (f.symm.trans g) := by
    funext i
    simp
  rw [hv]
  exact symm_perm F hF _ _

omit [DecidableEq ι] [DecidableEq κ] in
theorem reindex_single [DecidableEq ι] [DecidableEq κ] (e' : ι ≃ κ) (a b : ι) :
    (Matrix.single a b (1 : ℂ)).reindex e' e' = Matrix.single (e' a) (e' b) 1 := by
  ext x y
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.single_apply, Equiv.eq_symm_apply]

theorem reindex_thm : Reindex := by
  intro ι κ _ _ _ _ e F hF
  rw [detD_eq_Dg, detD_eq_Dg,
    ← Dg_indep F hF (e.symm.trans (Fintype.equivFin ι)) (Fintype.equivFin κ)]
  unfold Dg
  refine Fintype.sum_equiv (Equiv.permCongr e) _ _ fun σ => ?_
  rw [Equiv.Perm.sign_permCongr]
  congr 1
  have h1 : iteratedFDeriv ℂ (Fintype.card ι) (fun T => F (Matrix.reindex e e T)) 0
      (fun i => Matrix.single ((Fintype.equivFin ι).symm i) (σ ((Fintype.equivFin ι).symm i)) (1 : ℂ)) =
      iteratedFDeriv ℂ (Fintype.card ι) F 0 (fun i =>
        Matrix.reindex e e (Matrix.single ((Fintype.equivFin ι).symm i)
          (σ ((Fintype.equivFin ι).symm i)) (1 : ℂ))) :=
    iteratedFDeriv_comp_clm F hF
      (LinearMap.toContinuousLinearMap (Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap) _ _
  rw [h1]
  congr 1
  funext i
  rw [reindex_single]
  simp

omit [Fintype ι] in
theorem mul_single_eq [Fintype ι] (A : Matrix ι ι ℂ) (a b : ι) :
    A * Matrix.single a b (1 : ℂ) = ∑ c, A c a • Matrix.single c b (1 : ℂ) := by
  ext i j
  simp [Matrix.mul_apply, Matrix.single_apply, Matrix.sum_apply, ite_and]

private theorem sum_sign_iteratedFDeriv_single_eq_zero_of_not_inj (F : Matrix ι ι ℂ → ℂ) (hF : AnalyticAt ℂ F 0) {n : ℕ}
    (a : Fin n ≃ ι) (r : Fin n → ι) (hr : ¬ Function.Injective r) :
    ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) *
      iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (r k) (σ (a k)) (1 : ℂ)) = 0 := by
  obtain ⟨i, j, hij, hne⟩ : ∃ i j, r i = r j ∧ i ≠ j := by
    simp only [Function.Injective, not_forall] at hr
    obtain ⟨i, j, h, hne⟩ := hr
    exact ⟨i, j, h, hne⟩
  have hane : a i ≠ a j := fun h => hne (a.injective h)
  have key : ∀ σ : Equiv.Perm ι, iteratedFDeriv ℂ n F 0
      (fun k => Matrix.single (r k) ((σ * Equiv.swap (a i) (a j)) (a k)) (1 : ℂ)) =
      iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (r k) (σ (a k)) (1 : ℂ)) := by
    intro σ
    rw [← symm_perm F hF (fun k => Matrix.single (r k) (σ (a k)) (1 : ℂ)) (Equiv.swap i j)]
    congr 1
    funext k
    simp only [Equiv.Perm.mul_apply, Function.comp_apply]
    by_cases hki : k = i
    · subst hki
      rw [Equiv.swap_apply_left, Equiv.swap_apply_left, hij]
    · by_cases hkj : k = j
      · subst hkj
        rw [Equiv.swap_apply_right, Equiv.swap_apply_right, hij]
      · have h1 : a k ≠ a i := fun h => hki (a.injective h)
        have h2 : a k ≠ a j := fun h => hkj (a.injective h)
        rw [Equiv.swap_apply_of_ne_of_ne h1 h2, Equiv.swap_apply_of_ne_of_ne hki hkj]
  have hS := (Equiv.sum_comp (Equiv.mulRight (Equiv.swap (a i) (a j)))
    (fun σ : Equiv.Perm ι => ((Equiv.Perm.sign σ : ℤ) : ℂ) *
      iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (r k) (σ (a k)) (1 : ℂ)))).symm
  have hg : ∀ σ : Equiv.Perm ι, ((Equiv.Perm.sign (σ * Equiv.swap (a i) (a j)) : ℤ) : ℂ) *
      iteratedFDeriv ℂ n F 0
        (fun k => Matrix.single (r k) ((σ * Equiv.swap (a i) (a j)) (a k)) (1 : ℂ)) =
      -(((Equiv.Perm.sign σ : ℤ) : ℂ) *
        iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (r k) (σ (a k)) (1 : ℂ))) := by
    intro σ
    rw [key σ, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hane]
    push_cast
    ring
  simp only [Equiv.coe_mulRight] at hS
  rw [Finset.sum_congr rfl (fun σ _ => hg σ), Finset.sum_neg_distrib] at hS
  have h2 : (2 : ℂ) * ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) *
      iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (r k) (σ (a k)) (1 : ℂ)) = 0 := by
    linear_combination hS
  simpa using h2

private theorem sum_sign_iteratedFDeriv_single_perm_eq_sign_mul (F : Matrix ι ι ℂ → ℂ) (hF : AnalyticAt ℂ F 0) {n : ℕ}
    (a : Fin n ≃ ι) (ρ : Equiv.Perm ι) :
    ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) *
      iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (ρ (a k)) (σ (a k)) (1 : ℂ)) =
    ((Equiv.Perm.sign ρ : ℤ) : ℂ) * ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) *
      iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (a k) (σ (a k)) (1 : ℂ)) := by
  have hterm : ∀ σ : Equiv.Perm ι,
      iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (ρ (a k)) (σ (a k)) (1 : ℂ)) =
      iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (a k) ((σ * ρ⁻¹) (a k)) (1 : ℂ)) := by
    intro σ
    rw [← symm_perm F hF (fun k => Matrix.single (a k) ((σ * ρ⁻¹) (a k)) (1 : ℂ))
      ((a.trans ρ).trans a.symm)]
    congr 1
    funext k
    simp [Equiv.Perm.mul_apply]
  calc ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (ρ (a k)) (σ (a k)) (1 : ℂ))
      = ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (a k) ((σ * ρ⁻¹) (a k)) (1 : ℂ)) :=
        Finset.sum_congr rfl fun σ _ => by rw [hterm σ]
    _ = ∑ τ : Equiv.Perm ι, ((Equiv.Perm.sign (τ * ρ) : ℤ) : ℂ) *
        iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (a k) ((τ * ρ * ρ⁻¹) (a k)) (1 : ℂ)) :=
        (Equiv.sum_comp (Equiv.mulRight ρ) (fun σ : Equiv.Perm ι => ((Equiv.Perm.sign σ : ℤ) : ℂ) *
          iteratedFDeriv ℂ n F 0
            (fun k => Matrix.single (a k) ((σ * ρ⁻¹) (a k)) (1 : ℂ)))).symm
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [mul_inv_cancel_right, Equiv.Perm.sign_mul]
        push_cast
        ring

theorem equivar_thm : Equivar := by
  intro ι _ _ F A hF
  let a : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let L : Matrix ι ι ℂ →L[ℂ] Matrix ι ι ℂ :=
    LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℂ A)
  have hΦ : ∀ σ : Equiv.Perm ι,
      iteratedFDeriv ℂ (Fintype.card ι) (fun T => F (A * T)) 0
        (fun i => Matrix.single (a i) (σ (a i)) (1 : ℂ)) =
      ∑ r : Fin (Fintype.card ι) → ι, (∏ i, A (r i) (a i)) *
        iteratedFDeriv ℂ (Fintype.card ι) F 0 (fun i => Matrix.single (r i) (σ (a i)) (1 : ℂ)) := by
    intro σ
    have h1 : iteratedFDeriv ℂ (Fintype.card ι) (fun T => F (A * T)) 0
        (fun i => Matrix.single (a i) (σ (a i)) (1 : ℂ)) =
        iteratedFDeriv ℂ (Fintype.card ι) F 0
          (fun i => A * Matrix.single (a i) (σ (a i)) (1 : ℂ)) :=
      iteratedFDeriv_comp_clm F hF L _ _
    rw [h1]
    simp_rw [mul_single_eq]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [ContinuousMultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul]
  have hswap : detD (fun T => F (A * T)) = ∑ r : Fin (Fintype.card ι) → ι,
      (∏ i, A (r i) (a i)) * ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        iteratedFDeriv ℂ (Fintype.card ι) F 0 (fun i => Matrix.single (r i) (σ (a i)) (1 : ℂ)) := by
    unfold detD
    rw [Finset.sum_congr rfl fun σ _ => by rw [hΦ σ]]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun σ _ => ?_
    ring
  rw [hswap]
  have hinj : ∀ ρ ∈ (Finset.univ : Finset (Equiv.Perm ι)), ∀ ρ' ∈ (Finset.univ : Finset (Equiv.Perm ι)),
      (fun i => ρ (a i)) = (fun i => ρ' (a i)) → ρ = ρ' := by
    intro ρ _ ρ' _ h
    ext x
    simpa [a] using congrFun h (Fintype.equivFin ι x)
  rw [← Finset.sum_subset (Finset.subset_univ
      ((Finset.univ : Finset (Equiv.Perm ι)).image fun ρ => (fun i => ρ (a i)))),
    Finset.sum_image hinj]
  · have hD : detD F = ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        iteratedFDeriv ℂ (Fintype.card ι) F 0 (fun k => Matrix.single (a k) (σ (a k)) (1 : ℂ)) := rfl
    simp_rw [sum_sign_iteratedFDeriv_single_perm_eq_sign_mul F hF a, ← hD]
    rw [Matrix.det_apply', Finset.sum_mul]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [show (∏ i, A (ρ (a i)) (a i)) = ∏ x, A (ρ x) x from Equiv.prod_comp a (fun x => A (ρ x) x)]
    ring
  · intro r _ hr
    rw [sum_sign_iteratedFDeriv_single_eq_zero_of_not_inj F hF a r ?_, mul_zero]
    intro hr'
    apply hr
    rw [Finset.mem_image]
    refine ⟨Equiv.ofBijective (fun x => r (a.symm x))
      ((hr'.comp a.symm.injective).bijective_of_finite), Finset.mem_univ _, ?_⟩
    funext i
    simp

end PositivityTheory.Rg.Sw.LVs.CEq

namespace PositivityTheory.Rg.Sw.LVs

theorem equivar : Equivar := CEq.equivar_thm

theorem reindex : Reindex := CEq.reindex_thm

end PositivityTheory.Rg.Sw.LVs
end
end
