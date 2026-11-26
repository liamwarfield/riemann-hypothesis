module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.RaisingLoweringNormIdentities
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.NChart

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.SmInfUnitary
noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base

theorem smInfUnitary : SmInfUnitaryStatement :=
  fun _ _ _ _ _ _ hσ => isInfUnitary_of_isDerivedOn hσ (isDerivedOn_smE hσ)

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.InvMulSelfOfMemIndefiniteUnitary
noncomputable section

open Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

private theorem Jm_mul_selfDiscreteSeriesExistence (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

private theorem Jm_conjTransposeDiscreteSeriesExistence (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  unfold Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  change star (if ε a = true then (1 : ℂ) else -1) = _
  split_ifs <;> simp

private theorem Jm_mul_Jm_mul_eq (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) :
    Jm ε * (Jm ε * Y) = Y := by
  rw [← Matrix.mul_assoc, Jm_mul_selfDiscreteSeriesExistence, Matrix.one_mul]

theorem inv_eq_signature_conjTranspose_conj {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    g⁻¹ = Jm ε * gᴴ * Jm ε := by
  have h : gᴴ * Jm ε * g = Jm ε := hg
  apply Matrix.inv_eq_left_inv
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, h, Jm_mul_selfDiscreteSeriesExistence]

theorem inv_mul_self_of_mem_indefiniteUnitary {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    g⁻¹ * g = 1 := by
  have h : gᴴ * Jm ε * g = Jm ε := hg
  rw [inv_eq_signature_conjTranspose_conj hg, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, h, Jm_mul_selfDiscreteSeriesExistence]

theorem mul_inv_self_of_mem_indefiniteUnitary {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g (Matrix.isUnit_det_of_left_inverse (inv_mul_self_of_mem_indefiniteUnitary hg))

theorem isUnit_of_mem_indefiniteUnitary {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) : IsUnit g :=
  ⟨⟨g, g⁻¹, mul_inv_self_of_mem_indefiniteUnitary hg, inv_mul_self_of_mem_indefiniteUnitary hg⟩, rfl⟩

theorem inG_conj_unitary {ε : Fin n → Bool} {g X : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε)
    (hX : inG ε X) : inG ε (g * X * g⁻¹) := by
  have hJ : Jm ε * Jm ε = 1 := Jm_mul_selfDiscreteSeriesExistence ε
  have hJh : (Jm ε)ᴴ = Jm ε := Jm_conjTransposeDiscreteSeriesExistence ε
  have hX0 : Xᴴ * Jm ε + Jm ε * X = 0 := hX
  have hX' : Jm ε * Xᴴ + X * Jm ε = 0 := by
    have e : Jm ε * Xᴴ + X * Jm ε = Jm ε * (Xᴴ * Jm ε + Jm ε * X) * Jm ε := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, hJ, Matrix.mul_one,
        Jm_mul_Jm_mul_eq]
    rw [e, hX0, Matrix.mul_zero, Matrix.zero_mul]
  have key : (g * X * g⁻¹)ᴴ * Jm ε + Jm ε * (g * X * g⁻¹) =
      Jm ε * g * (Jm ε * Xᴴ + X * Jm ε) * gᴴ * Jm ε := by
    rw [inv_eq_signature_conjTranspose_conj hg]
    simp only [Matrix.conjTranspose_mul, hJh, Matrix.conjTranspose_conjTranspose, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_assoc]
  show (g * X * g⁻¹)ᴴ * Jm ε + Jm ε * (g * X * g⁻¹) = 0
  rw [key, hX', Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul]

private theorem Jm_conjTranspose_Jm_eq_neg_of_inG {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    Jm ε * Xᴴ * Jm ε = -X := by
  have h0 : Xᴴ * Jm ε + Jm ε * X = 0 := hX
  have h1 : Xᴴ * Jm ε = -(Jm ε * X) := eq_neg_of_add_eq_zero_left h0
  rw [Matrix.mul_assoc, h1, Matrix.mul_neg, Jm_mul_Jm_mul_eq]

theorem conj_involution_complex_comb {ε : Fin n → Bool} {A B : Matrix (Fin n) (Fin n) ℂ} (hA : inG ε A) (hB : inG ε B) :
    stJ ε (A + Complex.I • B) = -A + Complex.I • B := by
  unfold stJ
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, Jm_conjTranspose_Jm_eq_neg_of_inG hA, Jm_conjTranspose_Jm_eq_neg_of_inG hB]
  simp [Complex.star_def, Complex.conj_I]

theorem actM_add_smul {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (X Y : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) :
    actM E (X + c • Y) = actM E X + c • actM E Y := by
  simp only [actM, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_smul, mul_smul,
    Finset.sum_add_distrib, Finset.smul_sum]

theorem actM_neg {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (X : Matrix (Fin n) (Fin n) ℂ) : actM E (-X) = -actM E X := by
  simp only [actM, Matrix.neg_apply, neg_smul, Finset.sum_neg_distrib]

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem isometry_inner_eq {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {h : Matrix (Fin n) (Fin n) ℂ}
    (hn : ∀ v : H, ‖σ h v‖ = ‖v‖) (a b : H) : ⟪σ h a, σ h b⟫_ℂ = ⟪a, b⟫_ℂ := by
  exact LinearIsometry.inner_map_map
    ({ toLinearMap := (σ h : H →ₗ[ℂ] H), norm_map' := hn } : H →ₗᵢ[ℂ] H) a b

theorem derived_action_skew_adjoint {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) {w : H} (hw : w ∈ smD ε σ) {Y : Matrix (Fin n) (Fin n) ℂ}
    (hY : inG ε Y) {u u' : H}
    (hu : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • Y)) u) u' 0) :
    ⟪w, u'⟫_ℂ = -⟪((actM (smE ε σ) Y ⟨w, hw⟩ : smD ε σ) : H), u⟫_ℂ := by
  have hd := (isDerivedOn_smE hσ).deriv Y hY ⟨w, hw⟩
  have h3 : HasDerivAt
      (fun t : ℝ => ⟪σ (NormedSpace.exp ((t : ℂ) • Y)) w, σ (NormedSpace.exp ((t : ℂ) • Y)) u⟫_ℂ)
      (⟪σ (NormedSpace.exp (((0 : ℝ) : ℂ) • Y)) w, u'⟫_ℂ +
        ⟪((actM (smE ε σ) Y ⟨w, hw⟩ : smD ε σ) : H), σ (NormedSpace.exp (((0 : ℝ) : ℂ) • Y)) u⟫_ℂ) 0 :=
    hd.inner ℂ hu
  have h4 : (fun t : ℝ =>
      ⟪σ (NormedSpace.exp ((t : ℂ) • Y)) w, σ (NormedSpace.exp ((t : ℂ) • Y)) u⟫_ℂ) =
      fun _ => ⟪w, u⟫_ℂ :=
    funext fun t => isometry_inner_eq (hσ.2.1 _ (exp_smul_mem_UJset hY t)) w u
  rw [h4] at h3
  have h5 := h3.unique (hasDerivAt_const (0 : ℝ) ⟪w, u⟫_ℂ)
  have h0 : NormedSpace.exp (((0 : ℝ) : ℂ) • Y) = 1 := by simp
  rw [h0, hσ.1.1] at h5
  simp only [ContinuousLinearMap.one_apply] at h5
  exact eq_neg_of_add_eq_zero_left h5

theorem hasDerivAt_conj_exp_action {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) {w : H} (hw : w ∈ smD ε σ) {g X : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) (hX : inG ε X) :
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹))) (σ g w))
      (σ g ((actM (smE ε σ) X ⟨w, hw⟩ : smD ε σ) : H)) 0 := by
  have hgX : inG ε (g * X * g⁻¹) := inG_conj_unitary hg hX
  have hd := (isDerivedOn_smE hσ).deriv X hX ⟨w, hw⟩
  have hfun : (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹))) (σ g w)) =
      fun t : ℝ => σ g (σ (NormedSpace.exp ((t : ℂ) • X)) w) := by
    funext t
    have hm : NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹)) * g = g * NormedSpace.exp ((t : ℂ) • X) := by
      rw [show (t : ℂ) • (g * X * g⁻¹) = g * ((t : ℂ) • X) * g⁻¹ by
          rw [Matrix.mul_smul, Matrix.smul_mul],
        Matrix.exp_conj g _ (isUnit_of_mem_indefiniteUnitary hg), Matrix.mul_assoc, inv_mul_self_of_mem_indefiniteUnitary hg, Matrix.mul_one]
    have h1 := hσ.1.2 _ (exp_smul_mem_UJset hgX t) g hg
    have h2 := hσ.1.2 g hg _ (exp_smul_mem_UJset hX t)
    rw [hm] at h1
    exact congrArg (fun L : H →L[ℂ] H => L w) (h1.symm.trans h2)
  rw [hfun]
  exact ((σ g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hd

end Rep

private theorem inG_of_Jm_conj_eq_neg {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ}
    (h : Jm ε * Yᴴ * Jm ε = -Y) : inG ε Y := by
  show Yᴴ * Jm ε + Jm ε * Y = 0
  have e : Yᴴ * Jm ε = Jm ε * (Jm ε * Yᴴ * Jm ε) := by
    rw [Matrix.mul_assoc (Jm ε) Yᴴ, Jm_mul_Jm_mul_eq]
  rw [e, h, Matrix.mul_neg, neg_add_cancel]

private theorem exists_inG_add_I_smul_inG (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    ∃ A B : Matrix (Fin n) (Fin n) ℂ, inG ε A ∧ inG ε B ∧ X = A + Complex.I • B := by
  have hJ : Jm ε * Jm ε = 1 := Jm_mul_selfDiscreteSeriesExistence ε
  have hJh : (Jm ε)ᴴ = Jm ε := Jm_conjTransposeDiscreteSeriesExistence ε
  refine ⟨(1 / 2 : ℂ) • (X - Jm ε * Xᴴ * Jm ε), (1 / (2 * Complex.I)) • (X + Jm ε * Xᴴ * Jm ε),
    ?_, ?_, ?_⟩
  · apply inG_of_Jm_conj_eq_neg
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hJh,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_assoc, hJ, Matrix.mul_one, Jm_mul_Jm_mul_eq]
    rw [show star (1 / 2 : ℂ) = 1 / 2 by simp, ← smul_neg, neg_sub]
  · apply inG_of_Jm_conj_eq_neg
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, hJh,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_assoc, hJ, Matrix.mul_one, Jm_mul_Jm_mul_eq]
    have hc : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
      simp [Complex.star_def, Complex.conj_I]
    rw [hc, neg_smul, add_comm (Jm ε * (Xᴴ * Jm ε)) X]
  · have hI : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by
      rw [mul_one_div, mul_comm 2 Complex.I, ← div_div, div_self Complex.I_ne_zero]
    have h2 : X - Jm ε * Xᴴ * Jm ε + (X + Jm ε * Xᴴ * Jm ε) = (2 : ℂ) • X := by
      rw [two_smul]; abel
    rw [smul_smul, hI, ← smul_add, h2, smul_smul]
    norm_num

theorem b3a : MatrixCoeffConjugationMove := by
  intro n ε H _ _ σ w hσ hw g hg X
  have hφ : ∀ Y, phiW ε σ w Y = ((actM (smE ε σ) Y ⟨w, hw⟩ : smD ε σ) : H) := fun Y => by
    simp only [phiW, dif_pos hw]
  have hlin : ∀ (Y Z : Matrix (Fin n) (Fin n) ℂ) (c : ℂ),
      ((actM (smE ε σ) (Y + c • Z) ⟨w, hw⟩ : smD ε σ) : H) =
        ((actM (smE ε σ) Y ⟨w, hw⟩ : smD ε σ) : H) +
          c • ((actM (smE ε σ) Z ⟨w, hw⟩ : smD ε σ) : H) := by
    intro Y Z c
    rw [actM_add_smul]
    simp
  have hneg : ∀ Y, ((actM (smE ε σ) (-Y) ⟨w, hw⟩ : smD ε σ) : H) =
      -((actM (smE ε σ) Y ⟨w, hw⟩ : smD ε σ) : H) := by
    intro Y
    rw [actM_neg]
    simp
  have key : ∀ Y, inG ε Y → ⟪w, σ g ((actM (smE ε σ) Y ⟨w, hw⟩ : smD ε σ) : H)⟫_ℂ =
      -⟪((actM (smE ε σ) (g * Y * g⁻¹) ⟨w, hw⟩ : smD ε σ) : H), σ g w⟫_ℂ :=
    fun Y hY => derived_action_skew_adjoint hσ hw (inG_conj_unitary hg hY) (hasDerivAt_conj_exp_action hσ hw hg hY)
  obtain ⟨A, B, hA, hB, rfl⟩ := exists_inG_add_I_smul_inG ε X
  have hconj : g * (A + Complex.I • B) * g⁻¹ = g * A * g⁻¹ + Complex.I • (g * B * g⁻¹) := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [hconj, conj_involution_complex_comb (inG_conj_unitary hg hA) (inG_conj_unitary hg hB), hφ, hφ, hlin, hlin, hneg,
    map_add, map_smul, inner_add_right, inner_smul_right, inner_add_left, inner_smul_left,
    inner_neg_left, key A hA, key B hB]
  simp only [Complex.conj_I]
  ring

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.B3b
noncomputable section

open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base

open ReciprocityTheory.ChartRestriction.DS

theorem b3b : DerivMatrixCoeffExp := by
  intro n ε H _ _ σ w hσ hw Z hZ s
  have h0 := (isDerivedOn_smE hσ).deriv Z hZ ⟨w, hw⟩
  have hphi : phiW ε σ w Z = ((actM (smE ε σ) Z ⟨w, hw⟩ : smD ε σ) : H) := by
    simp only [phiW, dif_pos hw]
  set g := σ (NormedSpace.exp ((s : ℂ) • Z)) with hg
  set T : H →L[ℂ] ℂ := (innerSL ℂ w).comp g with hT
  have h1 := ((T.restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt (0 : ℝ) h0
  have h2 : HasDerivAt (fun x : ℝ => T (σ (NormedSpace.exp (((x - s : ℝ) : ℂ) • Z)) w))
      (T ((actM (smE ε σ) Z ⟨w, hw⟩ : smD ε σ) : H)) s := by
    have h1' : HasDerivAt (⇑(ContinuousLinearMap.restrictScalars ℝ T) ∘
        fun t : ℝ => (σ (NormedSpace.exp ((t : ℂ) • Z))) w)
        ((ContinuousLinearMap.restrictScalars ℝ T) ((actM (smE ε σ) Z ⟨w, hw⟩ : smD ε σ) : H)) (s - s) := by
      rw [sub_self]; exact h1
    exact h1'.comp_sub_const s s
  rw [hphi]
  convert (preTransparency := .reducible) h2 using 1
  · funext x
    have he : NormedSpace.exp ((x : ℂ) • Z) =
        NormedSpace.exp ((s : ℂ) • Z) * NormedSpace.exp (((x - s : ℝ) : ℂ) • Z) := by
      rw [← exp_add_smul]
      congr 2
      push_cast
      ring
    rw [he, hσ.1.2 _ (exp_smul_mem_UJset hZ s) _ (exp_smul_mem_UJset hZ (x - s))]
    simp [hT, hg]
  · simp [hT, hg]

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.UnipotentExpHaarSqrtBound
noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base
open ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
open Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S MeasureTheory

section Generic
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A]
  {F : ℕ → Submodule ℝ A} {L : ℕ} {st : A →ₗ[ℝ] A}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem haar_of_equiv [MeasurableSpace A] [BorelSpace A] [MeasurableSpace E] [BorelSpace E]
    (hF : IsFil F L) (hst : IsAdj F st) (μ : Measure E) [μ.IsAddHaarMeasure]
    (e : E ≃ₗ[ℝ] lieN F st) :
    SigmaFinite (μ.map fun x => NormedSpace.exp (e x : A)) ∧
      (μ.map fun x => NormedSpace.exp (e x : A)) ≠ 0 ∧
      (μ.map fun x => NormedSpace.exp (e x : A)) {x | x ∉ grpN F st} = 0 ∧
      ∀ s ∈ grpN F st, (μ.map fun x => NormedSpace.exp (e x : A)).map (s * ·) =
        μ.map fun x => NormedSpace.exp (e x : A) := by
  let e' := e.toContinuousLinearEquiv
  have : (Measure.map e' μ).IsAddHaarMeasure := e'.isAddHaarMeasure_map μ
  have h := exp_chart_haar hF hst (Measure.map e' μ)
  have he := exp_chart_embedding (st := st) hF
  simp only [] at h
  rw [Measure.map_map he.measurable e'.continuous.measurable] at h
  exact h

omit [FiniteDimensional ℝ A] in
theorem growth_of_equiv (hF : IsFil F L) (U0 : E ≃ₗ[ℝ] A) : ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧ ∀ Y ∈ F 0,
    ‖U0.symm Y‖ ≤ C * ‖U0.symm (NormedSpace.exp Y - 1)‖ *
      (1 + ‖U0.symm (NormedSpace.exp Y - 1)‖) ^ M := by
  obtain ⟨C, M, hC, h⟩ := hF.log_growth
  let U := U0.toContinuousLinearEquiv
  set a := ‖(U.symm : A →L[ℝ] E)‖ with ha
  set b := ‖(U : E →L[ℝ] A)‖ with hb
  have ha0 : 0 ≤ a := norm_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  have h1 : ∀ X, ‖U0.symm X‖ ≤ a * ‖X‖ := fun X => (U.symm : A →L[ℝ] E).le_opNorm X
  have h2 : ∀ X, ‖X‖ ≤ b * ‖U0.symm X‖ := fun X => by
    have := (U : E →L[ℝ] A).le_opNorm (U.symm X)
    rwa [ContinuousLinearEquiv.coe_coe, U.apply_symm_apply] at this
  refine ⟨a * C * b * (1 + b) ^ M, M, by positivity, fun Y hY => ?_⟩
  set s := ‖U0.symm (NormedSpace.exp Y - 1)‖ with hs
  have hs0 : 0 ≤ s := norm_nonneg _
  have h3 := h2 (NormedSpace.exp Y - 1)
  have h4 : 1 + ‖NormedSpace.exp Y - 1‖ ≤ (1 + b) * (1 + s) := by nlinarith
  calc ‖U0.symm Y‖ ≤ a * ‖Y‖ := h1 Y
    _ ≤ a * (C * ‖NormedSpace.exp Y - 1‖ * (1 + ‖NormedSpace.exp Y - 1‖) ^ M) :=
        mul_le_mul_of_nonneg_left (h Y hY) ha0
    _ ≤ a * (C * (b * s) * ((1 + b) * (1 + s)) ^ M) := by gcongr
    _ = _ := by rw [mul_pow]; ring

end Generic

open scoped Matrix.Norms.Operator

noncomputable def unrealL (m : ℕ) :
    EuclideanSpace ℝ (Fin m × Fin m × Bool) ≃ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ where
  toFun := unrealify
  invFun X := (WithLp.equiv 2 _).symm (realifyFun X)
  map_add' x y := by ext i j; apply Complex.ext <;> simp [unrealify]
  map_smul' c x := by ext i j; apply Complex.ext <;> simp [unrealify]
  left_inv x := by
    ext ⟨i, j, b⟩
    cases b <;> simp [unrealify, realifyFun]
  right_inv X := by ext i j; apply Complex.ext <;> simp [unrealify, realifyFun]

theorem sqrt_hs {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) :
    Real.sqrt (S7.hs X) = ‖(unrealL m).symm X‖ := by
  rw [EuclideanSpace.norm_eq, S7.hs]
  congr 1
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  show ‖X i j‖ ^ 2 = ‖(X i j).im‖ ^ 2 + ‖(X i j).re‖ ^ 2
  rw [Complex.sq_norm, Complex.normSq_apply, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  ring

variable {k r : ℕ}

theorem lieE_eq : lieE (Nset k r) =
    (lieN (levF (levB k r)) (adjH (Hpk k r))).map (unrealL _).symm.toLinearMap := by
  rw [lieE, lieOf_Nset_eq, ← Submodule.span_eq (Submodule.map _ _)]
  rfl

theorem unipotent_exp_haar_sqrt_bound (k r : ℕ) :
    (∀ Y ∈ lieOf (Nset k r), ∀ Y' ∈ lieOf (Nset k r),
      NormedSpace.exp Y = NormedSpace.exp Y' → Y = Y') ∧
    (∀ g ∈ Nset k r, ∃ Y ∈ lieOf (Nset k r), NormedSpace.exp Y = g) ∧
    (∀ x : lieE (Nset k r), unrealify (x : EuclideanSpace ℝ _) ∈ lieOf (Nset k r)) ∧
    IsHaarOn (Nset k r) (haarLie (Nset k r) 1) ∧
    ∃ (C : ℝ) (m : ℕ), 0 ≤ C ∧ ∀ Y ∈ lieOf (Nset k r),
      Real.sqrt (S7.hs Y) ≤ C * Real.sqrt (S7.hs (NormedSpace.exp Y - 1)) *
        (1 + Real.sqrt (S7.hs (NormedSpace.exp Y - 1))) ^ m := by
  have hmem : ∀ x : lieE (Nset k r),
      unrealL _ (x : EuclideanSpace ℝ _) ∈ lieN (levF (levB k r)) (adjH (Hpk k r)) := by
    rintro ⟨x, hx⟩
    rw [lieE_eq] at hx
    obtain ⟨Y, hY, rfl⟩ := hx
    simpa using hY
  refine ⟨fun Y hY Y' hY' h => ?_, fun g hg => ?_, fun x => ?_, ?_, ?_⟩
  · rw [lieOf_Nset_eq] at hY hY'
    exact exp_injOn isFilB (mem_lieN.mp hY).1 (mem_lieN.mp hY').1 h
  · rw [Nset_eq] at hg
    rw [lieOf_Nset_eq]
    exact ⟨_, lg_spec isFilB isAdjB hg⟩
  · rw [lieOf_Nset_eq]; exact hmem x
  · let e : lieE (Nset k r) ≃ₗ[ℝ] lieN (levF (levB k r)) (adjH (Hpk k r)) :=
      { toFun := fun x => ⟨unrealL _ x, hmem x⟩
        invFun := fun Y => ⟨(unrealL _).symm Y, by rw [lieE_eq]; exact ⟨Y, Y.2, rfl⟩⟩
        map_add' := fun x y => Subtype.ext (map_add (unrealL _) _ _)
        map_smul' := fun c x => Subtype.ext (map_smul (unrealL _) _ _)
        left_inv := fun x => Subtype.ext ((unrealL _).symm_apply_apply _)
        right_inv := fun Y => Subtype.ext ((unrealL _).apply_symm_apply _) }
    have h := @haar_of_equiv (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
      Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra _ _ _ _ _ _ _ _
      (inferInstance : MeasurableSpace (Mt k r))
      (inferInstance : BorelSpace (Mt k r)) _ _ isFilB isAdjB volume _ e
    rw [← Nset_eq] at h
    rw [haarLie, one_smul]
    exact h
  · obtain ⟨C, M, hC, h⟩ := growth_of_equiv (isFilB (k := k) (r := r)) (unrealL (2 * r + k + 1))
    refine ⟨C, M, hC, fun Y hY => ?_⟩
    rw [lieOf_Nset_eq] at hY
    rw [sqrt_hs, sqrt_hs]
    exact h Y (mem_lieN.mp hY).1

theorem b4 : NsetExpInjectiveSurjective := unipotent_exp_haar_sqrt_bound

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.NormMatrixTripleProductLe
noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.ConjugationTaylorBound

open scoped Nat

section Abstract

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]

theorem norm_exp_sub_one_sub_le (x : 𝔸) :
    ‖NormedSpace.exp x - 1 - x‖ ≤ ‖x‖ ^ 2 * Real.exp ‖x‖ := by
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) x
  have h2 := (hasSum_nat_add_iff' 2).mpr h
  have e : ∑ i ∈ Finset.range 2, ((i !⁻¹ : ℂ) • x ^ i) = 1 + x := by
    simp [Finset.sum_range_succ]
  rw [e, ← sub_sub] at h2
  have hr := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ‖x‖
  rw [← Real.exp_eq_exp_ℝ] at hr
  have hg := hr.mul_left (‖x‖ ^ 2)
  refine h2.norm_le_of_bounded hg ?_
  intro m
  rw [norm_smul, norm_inv, Complex.norm_natCast, smul_eq_mul]
  have hf : ((m + 2)! : ℝ)⁻¹ ≤ ((m ! : ℕ) : ℝ)⁻¹ := by
    apply inv_anti₀ (by exact_mod_cast Nat.factorial_pos m)
    exact_mod_cast Nat.factorial_le (by omega)
  have hp : ‖x ^ (m + 2)‖ ≤ ‖x‖ ^ (m + 2) := norm_pow_le' x (by omega)
  calc ((((m + 2)! : ℕ) : ℝ))⁻¹ * ‖x ^ (m + 2)‖ ≤ ((m ! : ℕ) : ℝ)⁻¹ * ‖x‖ ^ (m + 2) :=
        mul_le_mul hf hp (norm_nonneg _) (by positivity)
    _ = ‖x‖ ^ 2 * (((m ! : ℕ) : ℝ)⁻¹ * ‖x‖ ^ m) := by ring

theorem conj_identity (a b u M : 𝔸) :
    a * M * b - M - (u * M - M * u) =
      M * (b - 1 + u) - u * M * u + u * M * (b - 1 + u) + (a - 1 - u) * M -
        (a - 1 - u) * M * u + (a - 1 - u) * M * (b - 1 + u) := by
  noncomm_ring

theorem norm_six (a b c d e f : 𝔸) :
    ‖a - b + c + d - e + f‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ := by
  have h1 := norm_add_le (a - b + c + d - e) f
  have h2 := norm_sub_le (a - b + c + d) e
  have h3 := norm_add_le (a - b + c) d
  have h4 := norm_add_le (a - b) c
  have h5 := norm_sub_le a b
  linarith

theorem norm_matrix_triple_product_le (x y z : 𝔸) : ‖x * y * z‖ ≤ ‖x‖ * ‖y‖ * ‖z‖ :=
  (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))

theorem le3 {a b c A B C : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h1 : a ≤ A) (h2 : b ≤ B)
    (h3 : c ≤ C) : a * b * c ≤ A * B * C :=
  mul_le_mul (mul_le_mul h1 h2 hb (ha.trans h1)) h3 hc (mul_nonneg (ha.trans h1) (hb.trans h2))

theorem conj_taylor (Y M : 𝔸) (τ r m : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hY : ‖Y‖ ≤ r)
    (hM : ‖M‖ ≤ m) :
    ‖NormedSpace.exp ((τ : ℂ) • Y) * M * NormedSpace.exp (-((τ : ℂ) • Y)) - M -
        (τ : ℂ) • (Y * M - M * Y)‖ ≤
      m * (2 * r ^ 2 * Real.exp r + r ^ 2 + 2 * r ^ 3 * Real.exp r + r ^ 4 * Real.exp r ^ 2) *
        τ ^ 2 := by
  set u : 𝔸 := (τ : ℂ) • Y with hu
  have hr0 : 0 ≤ r := (norm_nonneg _).trans hY
  have hm0 : 0 ≤ m := (norm_nonneg _).trans hM
  have hsm : (τ : ℂ) • (Y * M - M * Y) = u * M - M * u := by
    rw [hu, smul_sub, smul_mul_assoc, mul_smul_comm]
  rw [hsm, conj_identity]
  set p : ℝ := τ * r with hp
  set E : ℝ := Real.exp r with hE
  set q : ℝ := p ^ 2 * E with hq
  have hp0 : 0 ≤ p := mul_nonneg hτ0 hr0
  have hE0 : 0 ≤ E := (Real.exp_pos r).le
  have hq0 : 0 ≤ q := mul_nonneg (pow_nonneg hp0 2) hE0
  have hu' : ‖u‖ ≤ p := by
    rw [hu, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hτ0]
    exact mul_le_mul_of_nonneg_left hY hτ0
  have hexp : Real.exp ‖u‖ ≤ E := by
    apply Real.exp_le_exp.mpr
    calc ‖u‖ ≤ p := hu'
      _ ≤ r := by rw [hp]; nlinarith
  have hA : ‖NormedSpace.exp u - 1 - u‖ ≤ q := by
    refine (norm_exp_sub_one_sub_le u).trans ?_
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hu' 2) hexp (Real.exp_pos _).le
      (pow_nonneg hp0 2)
  have hB : ‖NormedSpace.exp (-u) - 1 + u‖ ≤ q := by
    have := norm_exp_sub_one_sub_le (-u)
    rw [sub_neg_eq_add, norm_neg] at this
    refine this.trans ?_
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hu' 2) hexp (Real.exp_pos _).le
      (pow_nonneg hp0 2)
  set A := NormedSpace.exp u - 1 - u
  set B := NormedSpace.exp (-u) - 1 + u
  have t1 : ‖M * B‖ ≤ m * q :=
    (norm_mul_le _ _).trans (mul_le_mul hM hB (norm_nonneg _) hm0)
  have t2 : ‖u * M * u‖ ≤ p * m * p :=
    (norm_matrix_triple_product_le _ _ _).trans (le3 (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hu' hM hu')
  have t3 : ‖u * M * B‖ ≤ p * m * q :=
    (norm_matrix_triple_product_le _ _ _).trans (le3 (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hu' hM hB)
  have t4 : ‖A * M‖ ≤ q * m :=
    (norm_mul_le _ _).trans (mul_le_mul hA hM (norm_nonneg _) hq0)
  have t5 : ‖A * M * u‖ ≤ q * m * p :=
    (norm_matrix_triple_product_le _ _ _).trans (le3 (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hA hM hu')
  have t6 : ‖A * M * B‖ ≤ q * m * q :=
    (norm_matrix_triple_product_le _ _ _).trans (le3 (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hA hM hB)
  refine (norm_six _ _ _ _ _ _).trans ?_
  have hτ3 : τ ^ 3 ≤ τ ^ 2 := pow_le_pow_of_le_one hτ0 hτ1 (by norm_num)
  have hτ4 : τ ^ 4 ≤ τ ^ 2 := pow_le_pow_of_le_one hτ0 hτ1 (by norm_num)
  have key : m * q + p * m * p + p * m * q + q * m + q * m * p + q * m * q =
      m * (2 * r ^ 2 * E * τ ^ 2 + r ^ 2 * τ ^ 2 + 2 * r ^ 3 * E * τ ^ 3 + r ^ 4 * E ^ 2 * τ ^ 4) := by
    rw [hq, hp]; ring
  have c3 : 2 * r ^ 3 * E * τ ^ 3 ≤ 2 * r ^ 3 * E * τ ^ 2 :=
    mul_le_mul_of_nonneg_left hτ3 (by positivity)
  have c4 : r ^ 4 * E ^ 2 * τ ^ 4 ≤ r ^ 4 * E ^ 2 * τ ^ 2 :=
    mul_le_mul_of_nonneg_left hτ4 (by positivity)
  have fin : m * q + p * m * p + p * m * q + q * m + q * m * p + q * m * q ≤
      m * (2 * r ^ 2 * E + r ^ 2 + 2 * r ^ 3 * E + r ^ 4 * E ^ 2) * τ ^ 2 := by
    rw [key]
    have := mul_le_mul_of_nonneg_left (add_le_add (add_le_add (le_refl
      (2 * r ^ 2 * E * τ ^ 2 + r ^ 2 * τ ^ 2)) c3) c4) hm0
    linarith
  linarith

end Abstract

end ReciprocityTheory.ChartRestriction.DS.Lap.Base.ConjugationTaylorBound

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.ConjugationTaylorBound

section Op

open scoped NNReal

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}

theorem entry_le_op (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : ‖A i j‖ ≤ ‖A‖ := by
  have h : ‖A i j‖₊ ≤ ‖A‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    refine le_trans ?_ (Finset.le_sup (f := fun i : Fin n => ∑ j : Fin n, ‖A i j‖₊)
      (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j => ‖A i j‖₊) (fun _ _ => bot_le) (Finset.mem_univ j)
  exact_mod_cast h

theorem op_le_of_entry (A : Matrix (Fin n) (Fin n) ℂ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ i j, ‖A i j‖ ≤ c) : ‖A‖ ≤ n * c := by
  have h' : ‖A‖₊ ≤ (n : ℝ≥0) * c.toNNReal := by
    rw [Matrix.linfty_opNNNorm_def]
    apply Finset.sup_le
    intro i _
    calc ∑ j, ‖A i j‖₊ ≤ ∑ _j : Fin n, c.toNNReal :=
          Finset.sum_le_sum fun j _ => (by
            have := Real.toNNReal_le_toNNReal (h i j)
            rwa [norm_toNNReal] at this)
      _ = (n : ℝ≥0) * c.toNNReal := by simp
  have := NNReal.coe_le_coe.mpr h'
  push_cast [Real.coe_toNNReal _ hc] at this
  exact this

theorem conj_taylor_entry (R : ℝ) (hR : 0 ≤ R) (Y M : Matrix (Fin n) (Fin n) ℂ)
    (hY : ∀ i j, ‖Y i j‖ ≤ R) (hM : ∀ i j, ‖M i j‖ ≤ R) (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (i j : Fin n) :
    ‖(NormedSpace.exp ((τ : ℂ) • Y) * M * NormedSpace.exp (-((τ : ℂ) • Y)) - M -
        (τ : ℂ) • (Y * M - M * Y)) i j‖ ≤
      (n * R) * (2 * (n * R) ^ 2 * Real.exp (n * R) + (n * R) ^ 2 +
        2 * (n * R) ^ 3 * Real.exp (n * R) + (n * R) ^ 4 * Real.exp (n * R) ^ 2) * τ ^ 2 :=
  (entry_le_op _ i j).trans
    (conj_taylor Y M τ (n * R) (n * R) hτ0 hτ1 (op_le_of_entry Y R hR hY)
      (op_le_of_entry M R hR hM))

end Op

end ReciprocityTheory.ChartRestriction.DS.Lap.Base.ConjugationTaylorBound

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base

open ConjugationTaylorBound in
theorem b3c : ConjugationSecondOrderBound := by
  intro n R
  have hR : (0 : ℝ) ≤ max R 0 := le_max_right _ _
  refine ⟨(n * max R 0) * (2 * (n * max R 0) ^ 2 * Real.exp (n * max R 0) + (n * max R 0) ^ 2 +
        2 * (n * max R 0) ^ 3 * Real.exp (n * max R 0) +
        (n * max R 0) ^ 4 * Real.exp (n * max R 0) ^ 2), by positivity, ?_⟩
  intro Y M hY hM τ h0 h1
  have hY' : ∀ i j, ‖Y i j‖ ≤ max R 0 := fun i j =>
    (Matrix.norm_entry_le_entrywise_sup_norm Y).trans (hY.trans (le_max_left _ _))
  have hM' : ∀ i j, ‖M i j‖ ≤ max R 0 := fun i j =>
    (Matrix.norm_entry_le_entrywise_sup_norm M).trans (hM.trans (le_max_left _ _))
  exact (Matrix.norm_le_iff (by positivity)).2
    (fun i j => conj_taylor_entry (max R 0) hR Y M hY' hM' τ h0 h1 i j)

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.UnitaryHaarColumns
noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.StandardBasisEmbedding

open Formalism.QuantumDeterminants

variable {k r : ℕ}

def bl (k r : ℕ) (i : Fin (2 * r + k + 1)) : Prop := r ≤ i.val ∧ i.val < r + k

instance (i : Fin (2 * r + k + 1)) : Decidable (bl k r i) := by unfold bl; infer_instance

def eB (k r : ℕ) (q : Fin k) : Fin (2 * r + k + 1) := ⟨r + q.val, by omega⟩

private theorem eB_val_eq_add (q : Fin k) : (eB k r q).val = r + q.val := rfl

theorem eB_inj : Function.Injective (eB k r) := by
  intro a b hab
  have h1 := congrArg Fin.val hab
  rw [eB_val_eq_add, eB_val_eq_add] at h1
  exact Fin.ext (by omega)

theorem bl_eB (q : Fin k) : bl k r (eB k r q) := by
  have := q.isLt
  show r ≤ (eB k r q).val ∧ (eB k r q).val < r + k
  rw [eB_val_eq_add]
  omega

theorem ex_eB {i : Fin (2 * r + k + 1)} (hi : bl k r i) : ∃ q, i = eB k r q := by
  have hi' : r ≤ i.val ∧ i.val < r + k := hi
  refine ⟨⟨i.val - r, by omega⟩, Fin.ext ?_⟩
  rw [eB_val_eq_add]
  show i.val = r + (i.val - r)
  omega

theorem sumB (f : Fin (2 * r + k + 1) → ℂ) (hf : ∀ p, ¬ bl k r p → f p = 0) :
    ∑ p, f p = ∑ q : Fin k, f (eB k r q) := by
  rw [← Finset.sum_image (s := Finset.univ) (g := eB k r) (by intro a _ b _ hab; exact eB_inj hab)]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro p _ hp
  apply hf
  intro hb
  obtain ⟨q, rfl⟩ := ex_eB hb
  exact hp (Finset.mem_image_of_mem _ (Finset.mem_univ _))

private theorem blockW_apply_of_bl (h : Matrix (Fin k) (Fin k) ℂ) {i j : Fin (2 * r + k + 1)}
    (hi : bl k r i) (hj : bl k r j) :
    Formalism.MainNotions.S.blockW k r h i j =
      h ⟨i.val - r, by unfold bl at hi; omega⟩ ⟨j.val - r, by unfold bl at hj; omega⟩ := by
  have hi' : r ≤ i.val ∧ i.val < r + k := hi
  have hj' : r ≤ j.val ∧ j.val < r + k := hj
  simp only [Formalism.MainNotions.S.blockW, dif_pos hi', dif_pos hj']

theorem bw_ee (h : Matrix (Fin k) (Fin k) ℂ) (q q' : Fin k) :
    Formalism.MainNotions.S.blockW k r h (eB k r q) (eB k r q') = h q q' := by
  rw [blockW_apply_of_bl h (bl_eB q) (bl_eB q')]
  have e : ∀ (a : Fin k) (ha : (eB k r a).val - r < k), (⟨(eB k r a).val - r, ha⟩ : Fin k) = a :=
    fun a _ => Fin.ext (by show r + a.val - r = a.val; omega)
  rw [e, e]

theorem bw_col (h : Matrix (Fin k) (Fin k) ℂ) (i : Fin (2 * r + k + 1)) {j : Fin (2 * r + k + 1)}
    (hj : ¬ bl k r j) : Formalism.MainNotions.S.blockW k r h i j = if i = j then 1 else 0 := by
  have hj' : ¬ (r ≤ j.val ∧ j.val < r + k) := hj
  by_cases hi : r ≤ i.val ∧ i.val < r + k
  · have hne : i ≠ j := by
      intro e
      subst e
      exact hj' hi
    simp only [Formalism.MainNotions.S.blockW, dif_pos hi, dif_neg hj', if_neg hne]
  · simp only [Formalism.MainNotions.S.blockW, dif_neg hi]

theorem bw_row (h : Matrix (Fin k) (Fin k) ℂ) {i : Fin (2 * r + k + 1)} (j : Fin (2 * r + k + 1))
    (hi : ¬ bl k r i) : Formalism.MainNotions.S.blockW k r h i j = if i = j then 1 else 0 := by
  have hi' : ¬ (r ≤ i.val ∧ i.val < r + k) := hi
  simp only [Formalism.MainNotions.S.blockW, dif_neg hi']

theorem bw_off (h : Matrix (Fin k) (Fin k) ℂ) {i j : Fin (2 * r + k + 1)}
    (hi : ¬ bl k r i) (hj : bl k r j) : Formalism.MainNotions.S.blockW k r h i j = 0 := by
  have hi' : ¬ (r ≤ i.val ∧ i.val < r + k) := hi
  have hne : i ≠ j := by
    intro e
    subst e
    exact hi hj
  simp only [Formalism.MainNotions.S.blockW, dif_neg hi', if_neg hne]

theorem bw_off' (h : Matrix (Fin k) (Fin k) ℂ) {i j : Fin (2 * r + k + 1)}
    (hi : bl k r i) (hj : ¬ bl k r j) : Formalism.MainNotions.S.blockW k r h i j = 0 := by
  have hi' : r ≤ i.val ∧ i.val < r + k := hi
  have hj' : ¬ (r ≤ j.val ∧ j.val < r + k) := hj
  simp only [Formalism.MainNotions.S.blockW, dif_pos hi', dif_neg hj']

theorem blockW_mul (a b : Matrix (Fin k) (Fin k) ℂ) :
    Formalism.MainNotions.S.blockW k r (a * b) = Formalism.MainNotions.S.blockW k r a * Formalism.MainNotions.S.blockW k r b := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi : bl k r i
  · by_cases hj : bl k r j
    · obtain ⟨qi, rfl⟩ := ex_eB hi
      obtain ⟨qj, rfl⟩ := ex_eB hj
      rw [bw_ee, Matrix.mul_apply,
        sumB (fun p => Formalism.MainNotions.S.blockW k r a (eB k r qi) p * Formalism.MainNotions.S.blockW k r b p (eB k r qj))
          (fun p hp => by rw [bw_off' a (bl_eB qi) hp, zero_mul])]
      simp only [bw_ee]
    · simp only [fun l => bw_col b l hj, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte, bw_off' a hi hj, bw_off' (a * b) hi hj]
  · rw [bw_row _ j hi]
    simp only [fun l => bw_row a l hi, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte, bw_row b j hi]

theorem blockW_one : Formalism.MainNotions.S.blockW k r (1 : Matrix (Fin k) (Fin k) ℂ) = 1 := by
  ext i j
  rw [Matrix.one_apply]
  by_cases hi : bl k r i
  · by_cases hj : bl k r j
    · obtain ⟨qi, rfl⟩ := ex_eB hi
      obtain ⟨qj, rfl⟩ := ex_eB hj
      rw [bw_ee, Matrix.one_apply]
      simp only [eB_inj.eq_iff]
    · have hne : i ≠ j := by
        intro e
        subst e
        exact hj hi
      rw [bw_off' _ hi hj, if_neg hne]
  · exact bw_row _ j hi

theorem blockW_conjTranspose (h : Matrix (Fin k) (Fin k) ℂ) :
    (Formalism.MainNotions.S.blockW k r h)ᴴ = Formalism.MainNotions.S.blockW k r hᴴ := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  by_cases hi : bl k r i <;> by_cases hj : bl k r j
  · obtain ⟨qi, rfl⟩ := ex_eB hi
    obtain ⟨qj, rfl⟩ := ex_eB hj
    rw [bw_ee, bw_ee, Matrix.conjTranspose_apply]
  · rw [bw_off h hj hi, bw_off' _ hi hj, star_zero]
  · rw [bw_off' h hj hi, bw_off _ hi hj, star_zero]
  · rw [bw_row h i hj, bw_row _ j hi]
    by_cases e : i = j
    · subst e
      simp
    · rw [if_neg (Ne.symm e), if_neg e, star_zero]

theorem H_blrow {i : Fin (2 * r + k + 1)} (hi : bl k r i) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if i = j then 1 else 0 := by
  have hi' : r ≤ i.val ∧ i.val < r + k := hi
  simp only [Formalism.QuantumDeterminants.Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem H_blcol {j : Fin (2 * r + k + 1)} (hj : bl k r j) (i : Fin (2 * r + k + 1)) :
    Hpk k r i j = if i = j then 1 else 0 := by
  have hj' : r ≤ j.val ∧ j.val < r + k := hj
  simp only [Formalism.QuantumDeterminants.Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem H_lo {c : Fin (2 * r + k + 1)} (hc : c.val < r) (b : Fin (2 * r + k + 1)) :
    Hpk k r c b = if c.val + b.val = 2 * r + k then 1 else 0 := by
  have := b.isLt
  simp only [Formalism.QuantumDeterminants.Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem H_hi {c : Fin (2 * r + k + 1)} (hc : r + k < c.val) (b : Fin (2 * r + k + 1)) :
    Hpk k r c b = if c.val + b.val = 2 * r + k then 1 else 0 := by
  have := b.isLt
  simp only [Formalism.QuantumDeterminants.Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem H_mid {c : Fin (2 * r + k + 1)} (hc : c.val = r + k) (b : Fin (2 * r + k + 1)) :
    Hpk k r c b = if c = b then -1 else 0 := by
  have := b.isLt
  simp only [Formalism.QuantumDeterminants.Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem H_comm (h : Matrix (Fin k) (Fin k) ℂ) :
    Hpk k r * Formalism.MainNotions.S.blockW k r h = Formalism.MainNotions.S.blockW k r h * Hpk k r := by
  ext c d
  rw [Matrix.mul_apply, Matrix.mul_apply]
  by_cases hc : bl k r c
  · simp only [H_blrow hc, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    by_cases hd : bl k r d
    · simp only [H_blcol hd, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    · rw [bw_off' h hc hd]
      symm
      apply Finset.sum_eq_zero
      intro l _
      by_cases hl : bl k r l
      · have hne : l ≠ d := by
          intro e
          subst e
          exact hd hl
        rw [H_blrow hl d, if_neg hne, mul_zero]
      · rw [bw_off' h hc hl, zero_mul]
  · simp only [fun l => bw_row h l hc, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      ↓reduceIte]
    by_cases hd : bl k r d
    · have hne : c ≠ d := by
        intro e
        subst e
        exact hc hd
      rw [H_blcol hd c, if_neg hne]
      apply Finset.sum_eq_zero
      intro l _
      by_cases hl : bl k r l
      · have hne' : c ≠ l := by
          intro e
          subst e
          exact hc hl
        rw [H_blcol hl c, if_neg hne', zero_mul]
      · rw [bw_off h hl hd, mul_zero]
    · simp only [fun l => bw_col h l hd, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        ↓reduceIte]

theorem bw_mulVec {c : Fin (2 * r + k + 1)} (hc : ¬ bl k r c) (h : Matrix (Fin k) (Fin k) ℂ) :
    Formalism.MainNotions.S.blockW k r h *ᵥ bvec c = bvec c := by
  funext i
  simp only [Formalism.QuantumDeterminants.bvec, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  exact bw_col h i hc

theorem mem_UW {h : Matrix (Fin k) (Fin k) ℂ} (hu : h ∈ Matrix.unitaryGroup (Fin k) ℂ) :
    Formalism.MainNotions.S.blockW k r h ∈ UWset k r (z0 k r) := by
  have hs : hᴴ * h = 1 := by
    have hs' : star h * h = 1 := by
      first
        | exact Matrix.mem_unitaryGroup_iff'.mp hu
        | exact Unitary.star_mul_self_of_mem hu
        | exact hu.1
    rwa [Matrix.star_eq_conjTranspose] at hs'
  simp only [Formalism.QuantumDeterminants.UWset, Set.mem_setOf_eq]
  refine ⟨?_, fun a => ⟨?_, ?_⟩, ?_⟩
  · show (Formalism.MainNotions.S.blockW k r h)ᴴ * Hpk k r * Formalism.MainNotions.S.blockW k r h = Hpk k r
    rw [blockW_conjTranspose, Matrix.mul_assoc, H_comm, ← Matrix.mul_assoc, ← blockW_mul, hs,
      blockW_one, Matrix.one_mul]
  · apply bw_mulVec
    have := a.isLt
    show ¬ (r ≤ a.val ∧ a.val < r + k)
    omega
  · apply bw_mulVec
    have := a.isLt
    show ¬ (r ≤ 2 * r + k - a.val ∧ 2 * r + k - a.val < r + k)
    omega
  · show Formalism.MainNotions.S.blockW k r h *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.wI k r (Fin.last k)) =
      Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.wI k r (Fin.last k))
    apply bw_mulVec
    show ¬ (r ≤ r + k ∧ r + k < r + k)
    omega

end ReciprocityTheory.ChartRestriction.DS.Lap.Base.StandardBasisEmbedding
end
end
