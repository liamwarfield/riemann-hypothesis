module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WeilRepresentationQuadraticDatum
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DenominatorPowerSummable
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicLatticeMeasureFormula

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TotallyRealIntegralBasisExists
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TotallyRealIntegralBasisExists
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker

namespace GlobalTheory.CompanionTheory.SW.ThW

theorem exists_integralBasis_infinitePlace (F : Type) [Field F] [NumberField F]
    (hF : IsTotallyReal F) : Nonempty (Module.Basis (InfinitePlace F) ℤ (𝓞 F)) := by
  have hcard : Fintype.card (InfinitePlace F) = Module.finrank ℚ F := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank F
    have h3 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := F)
    have h2 : InfinitePlace.nrComplexPlaces F = 0 := IsTotallyReal.nrComplexPlaces_eq_zero F
    omega
  have e : Module.Free.ChooseBasisIndex ℤ (𝓞 F) ≃ InfinitePlace F :=
    Fintype.equivOfCardEq (by
      rw [hcard, ← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank])
  exact ⟨(RingOfIntegers.basis F).reindex e⟩

end GlobalTheory.CompanionTheory.SW.ThW
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TotallyRealIntegralBasisExistsStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.totally_real_integral_basis_exists : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → Nonempty (Module.Basis (InfinitePlace F) ℤ (𝓞 F)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThW.exists_integralBasis_infinitePlace | exact GlobalTheory.CompanionTheory.SW.ThW.exists_integralBasis_infinitePlace | (intros; apply GlobalTheory.CompanionTheory.SW.ThW.exists_integralBasis_infinitePlace <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramTransposeDualTraceIdentity
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramTransposeDualTraceIdentity
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ThW

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker

theorem DM_mulVec_emb {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]
    [DecidableEq (InfinitePlace F)] (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ))
    (y : ι → F) : DM B ρ *ᵥ emb ρ y = emb ρ (B *ᵥ y) := by
  funext p
  obtain ⟨i, w⟩ := p
  simp only [mulVec, dotProduct, DM, emb, Fintype.sum_prod_type, blockDiagonal_apply]
  rw [Finset.sum_comm]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, map_mul]

theorem gM_transpose_mulVec {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]
    [DecidableEq ι] [DecidableEq (InfinitePlace F)] (ρ : InfinitePlace F → (F →+* ℝ))
    (b : InfinitePlace F → 𝓞 F) (N : ℕ) (z : ι × InfinitePlace F → ℝ) (i : ι)
    (v : InfinitePlace F) :
    ((gM ρ b N)ᵀ *ᵥ z) (i, v) = (N : ℝ) * ∑ w, ρ w (b v : F) * z (i, w) := by
  simp only [mulVec, dotProduct, gM, transpose_apply, Matrix.smul_apply, kroneckerMap_apply, EM,
    Matrix.one_apply, Fintype.sum_prod_type, smul_eq_mul]
  rw [Finset.mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp [Finset.sum_ite_eq, mul_assoc]

theorem gM_DM_emb_eq_trace : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] [DecidableEq (InfinitePlace F)] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ (b : InfinitePlace F → 𝓞 F) (N : ℕ) (y : ι → F), (gM ρ b N)ᵀ *ᵥ (DM B ρ *ᵥ emb ρ y) = fun p => (((N : ℚ) * Algebra.trace ℚ F ((b p.2 : F) * (B *ᵥ y) p.1) : ℚ) : ℝ) := by
  intro F _ _ ι _ _ _ M B ρ P hQ b N y
  obtain ⟨hT, -, -, -, hρ, -, -⟩ := hQ
  funext p
  obtain ⟨i, v⟩ := p
  rw [DM_mulVec_emb, gM_transpose_mulVec]
  have h := sum_rho_eq_trace hT hρ ((b v : F) * (B *ᵥ y) i)
  simp only [emb, ← map_mul]
  rw [h]
  push_cast
  rfl

end GlobalTheory.CompanionTheory.SW.ThW
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramTransposeDualTraceIdentityStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_transpose_dual_trace_identity : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] [DecidableEq (InfinitePlace F)] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ (b : InfinitePlace F → 𝓞 F) (N : ℕ) (y : ι → F), (gM ρ b N)ᵀ *ᵥ (DM B ρ *ᵥ emb ρ y) = fun p => (((N : ℚ) * Algebra.trace ℚ F ((b p.2 : F) * (B *ᵥ y) p.1) : ℚ) : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThW.gM_DM_emb_eq_trace | exact GlobalTheory.CompanionTheory.SW.ThW.gM_DM_emb_eq_trace | (intros; apply GlobalTheory.CompanionTheory.SW.ThW.gM_DM_emb_eq_trace <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicCharacterExponentialFormula
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicCharacterExponentialFormula
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ThW

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups Kronecker

theorem DM_mulVec_emb_apply {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]
    [DecidableEq ι] [DecidableEq (InfinitePlace F)] (B : Matrix ι ι F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (y : ι → F) (i : ι) (w : InfinitePlace F) :
    (DM B ρ *ᵥ emb ρ y) (i, w) = ρ w ((B *ᵥ y) i) := by
  have h : ρ w ((B *ᵥ y) i) = ∑ j, ρ w (B i j) * ρ w (y j) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [mulVec, dotProduct, map_sum, map_mul]
  rw [h]
  simp only [mulVec, dotProduct, DM, emb, Fintype.sum_prod_type_right, blockDiagonal_apply]
  rw [Finset.sum_eq_single w]
  · simp
  · intro v _ hv
    simp [Ne.symm hv]
  · simp

theorem emb_dotProduct_DM {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]
    [DecidableEq ι] [DecidableEq (InfinitePlace F)] (B : Matrix ι ι F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (a y : ι → F) :
    emb ρ a ⬝ᵥ (DM B ρ *ᵥ emb ρ y) = ∑ w, ρ w (a ⬝ᵥ (B *ᵥ y)) := by
  have h : ∀ w, ρ w (a ⬝ᵥ (B *ᵥ y)) = ∑ i, ρ w (a i) * ρ w ((B *ᵥ y) i) := by
    intro w
    set_option synthInstance.maxHeartbeats 100000 in
      simp [dotProduct, map_sum, map_mul]
  simp only [h]
  rw [dotProduct, Fintype.sum_prod_type_right]
  simp only [DM_mulVec_emb_apply, emb]

theorem toA_dotProduct_Bf {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]
    (B : Matrix ι ι F) (a y : ι → F) :
    toA a ⬝ᵥ (Bf B *ᵥ toA y) = algebraMap F (A F) (a ⬝ᵥ (B *ᵥ y)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, mulVec, toA, Bf, map_sum, map_mul, Matrix.map_apply]

theorem chiB_toA_eq_exp (F : Type) [Field F] [NumberField F] (ψ : AddChar (A F) ℂ)
    (hψ : IsStdChar F ψ) (ι : Type) [Fintype ι] [DecidableEq ι]
    [DecidableEq (InfinitePlace F)] (M : ℕ) (B : Matrix ι ι F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ)
    (hQ : QSetup M B ρ P) (a y : ι → F) :
    chiB ψ (Bf B) (toA a) (toA y) = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) *
      ((emb ρ a ⬝ᵥ (DM B ρ *ᵥ emb ρ y) : ℝ) : ℂ)) := by
  obtain ⟨hT, -, -, -, hρ, -, -⟩ := hQ
  rw [chiB, toA_dotProduct_Bf, hψ.2, emb_dotProduct_DM, sum_rho_eq_trace hT hρ]
  norm_cast

end GlobalTheory.CompanionTheory.SW.ThW
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicCharacterExponentialFormulaStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_character_exponential_formula : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (A F) ℂ), IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [DecidableEq (InfinitePlace F)] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ a y : ι → F, chiB ψ (Bf B) (toA a) (toA y) = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((emb ρ a ⬝ᵥ (DM B ρ *ᵥ emb ρ y) : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThW.chiB_toA_eq_exp | exact GlobalTheory.CompanionTheory.SW.ThW.chiB_toA_eq_exp | (intros; apply GlobalTheory.CompanionTheory.SW.ThW.chiB_toA_eq_exp <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GaussianChangeOfVariablesIsometry
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GaussianChangeOfVariablesIsometry
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ThW.GaussOrth

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker

theorem quad_mulVec {ι : Type} [Fintype ι] [DecidableEq ι] (g M : Matrix ι ι ℝ) (x : ι → ℝ) :
    (g *ᵥ x) ⬝ᵥ (M *ᵥ (g *ᵥ x)) = x ⬝ᵥ ((gᵀ * M * g) *ᵥ x) := by
  have h : (gᵀ * M * g) *ᵥ x = gᵀ *ᵥ (M *ᵥ (g *ᵥ x)) := by
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [h, Matrix.dotProduct_mulVec x gᵀ, Matrix.vecMul_transpose]

theorem abs_det_eq_one {ι : Type} [Fintype ι] [DecidableEq ι] {g M : Matrix ι ι ℝ}
    (hM : M.det ≠ 0) (h : gᵀ * M * g = M) : |g.det| = 1 := by
  have h1 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h1
  have h2 : g.det * g.det = 1 := by
    apply mul_right_cancel₀ hM
    rw [one_mul]
    calc g.det * g.det * M.det = g.det * M.det * g.det := by ring
      _ = M.det := h1
  have h3 : |g.det| * |g.det| = 1 := by rw [← abs_mul, h2, abs_one]
  have h4 : 0 ≤ |g.det| := abs_nonneg _
  nlinarith [sq_nonneg (|g.det| - 1), sq_nonneg (|g.det| + 1)]

theorem measurePreserving_mulVec {ι : Type} [Fintype ι] [DecidableEq ι] {g : Matrix ι ι ℝ}
    (h : |g.det| = 1) : MeasurePreserving (fun x : ι → ℝ => g *ᵥ x) volume volume := by
  have hd : g.det ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at h
    exact zero_ne_one h
  refine ⟨(Continuous.matrix_mulVec continuous_const continuous_id).measurable, ?_⟩
  have := Real.map_matrix_volume_pi_eq_smul_volume_pi hd
  have e : (fun x : ι → ℝ => g *ᵥ x) = ⇑(Matrix.toLin' g) := by
    ext x i
    simp [Matrix.toLin'_apply]
  rw [e, this, abs_inv, h]
  simp

theorem measurableEmbedding_mulVec {W ι : Type} [Fintype W] [Fintype ι] [DecidableEq ι]
    {g : W → Matrix ι ι ℝ} (h : ∀ w, (g w).det ≠ 0) :
    MeasurableEmbedding (fun (x : W → ι → ℝ) (w : W) => g w *ᵥ x w) := by
  have hu : ∀ w, IsUnit (g w).det := fun w => isUnit_iff_ne_zero.mpr (h w)
  let e : (W → ι → ℝ) ≃ᵐ (W → ι → ℝ) :=
    { toFun := fun x w => g w *ᵥ x w
      invFun := fun x w => (g w)⁻¹ *ᵥ x w
      left_inv := by
        intro x
        funext w
        simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hu w), Matrix.one_mulVec]
      right_inv := by
        intro x
        funext w
        simp only [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hu w), Matrix.one_mulVec]
      measurable_toFun := by
        refine Continuous.measurable (continuous_pi fun w => ?_)
        exact Continuous.matrix_mulVec continuous_const (continuous_apply w)
      measurable_invFun := by
        refine Continuous.measurable (continuous_pi fun w => ?_)
        exact Continuous.matrix_mulVec continuous_const (continuous_apply w) }
  exact e.measurableEmbedding

theorem gauss_orth {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ)
    (gi : InfinitePlace F → Matrix ι ι ℝ) (hB : B.det ≠ 0)
    (hg : ∀ w, (gi w)ᵀ * B.map (ρ w) * gi w = B.map (ρ w)) :
    (∀ (τ : InfinitePlace F → ℂ) (x : InfinitePlace F → ι → ℝ),
      gauss B ρ P τ (fun w => gi w *ᵥ x w) = gauss B ρ (fun w => (gi w)ᵀ * P w * gi w) τ x) ∧
    ∀ τ : InfinitePlace F → ℂ, cG B ρ (fun w => (gi w)ᵀ * P w * gi w) τ = cG B ρ P τ := by
  have first : ∀ (τ : InfinitePlace F → ℂ) (x : InfinitePlace F → ι → ℝ),
      gauss B ρ P τ (fun w => gi w *ᵥ x w) = gauss B ρ (fun w => (gi w)ᵀ * P w * gi w) τ x := by
    intro τ x
    unfold gauss
    congr 1
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [quad_mulVec, quad_mulVec, hg w]
  refine ⟨first, fun τ => ?_⟩
  have hdet : ∀ w, (B.map (ρ w)).det ≠ 0 := by
    intro w
    have e : (B.map (ρ w)).det = ρ w B.det := (RingHom.map_det (ρ w) B).symm
    rw [e]
    exact (map_ne_zero (ρ w)).mpr hB
  have habs : ∀ w, |(gi w).det| = 1 := fun w => abs_det_eq_one (hdet w) (hg w)
  have hne : ∀ w, (gi w).det ≠ 0 := by
    intro w h0
    have := habs w
    rw [h0, abs_zero] at this
    exact zero_ne_one this
  have hmp : MeasurePreserving (fun (x : InfinitePlace F → ι → ℝ) w => gi w *ᵥ x w)
      volume volume :=
    volume_preserving_pi fun w => measurePreserving_mulVec (habs w)
  have hint := hmp.integral_comp (measurableEmbedding_mulVec hne) (gauss B ρ P τ)
  unfold cG
  rw [← hint]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => (first τ x).symm)

end GlobalTheory.CompanionTheory.SW.ThW.GaussOrth

theorem GlobalTheory.CompanionTheory.SW.ThW.gauss_orth_closed : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι F) (ρ : NumberField.InfinitePlace F → (F →+* ℝ)) (P : NumberField.InfinitePlace F → Matrix ι ι ℝ) (gi : NumberField.InfinitePlace F → Matrix ι ι ℝ), B.det ≠ 0 → (∀ w, (gi w).transpose * B.map (ρ w) * gi w = B.map (ρ w)) → (∀ (τ : NumberField.InfinitePlace F → ℂ) (x : NumberField.InfinitePlace F → ι → ℝ), GlobalTheory.CompanionTheory.SW.Core.gauss B ρ P τ (fun w => (gi w).mulVec (x w)) = GlobalTheory.CompanionTheory.SW.Core.gauss B ρ (fun w => (gi w).transpose * P w * gi w) τ x) ∧ ∀ τ : NumberField.InfinitePlace F → ℂ, GlobalTheory.CompanionTheory.SW.Core.cG B ρ (fun w => (gi w).transpose * P w * gi w) τ = GlobalTheory.CompanionTheory.SW.Core.cG B ρ P τ :=
  fun _ _ _ _ _ _ B ρ P gi hB hg => GlobalTheory.CompanionTheory.SW.ThW.GaussOrth.gauss_orth B ρ P gi hB hg
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GaussianChangeOfVariablesIsometryStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussian_change_of_variables_isometry : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ) (gi : InfinitePlace F → Matrix ι ι ℝ), B.det ≠ 0 → (∀ w, (gi w)ᵀ * B.map (ρ w) * gi w = B.map (ρ w)) → (∀ (τ : InfinitePlace F → ℂ) (x : InfinitePlace F → ι → ℝ), gauss B ρ P τ (fun w => gi w *ᵥ x w) = gauss B ρ (fun w => (gi w)ᵀ * P w * gi w) τ x) ∧ ∀ τ : InfinitePlace F → ℂ, cG B ρ (fun w => (gi w)ᵀ * P w * gi w) τ = cG B ρ P τ := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThW.gauss_orth_closed | exact GlobalTheory.CompanionTheory.SW.ThW.gauss_orth_closed | (intros; apply GlobalTheory.CompanionTheory.SW.ThW.gauss_orth_closed <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DualLatticeParametrization
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DualLatticeParametrization
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker

namespace GlobalTheory.CompanionTheory.SW.ThW.DualLattice

noncomputable def ratBasis {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (b : Module.Basis κ ℤ (𝓞 F)) : Module.Basis κ ℚ F :=
  b.localizationLocalization ℚ (nonZeroDivisors ℤ) F

theorem ratBasis_apply {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (b : Module.Basis κ ℤ (𝓞 F)) (v : κ) : ratBasis b v = (b v : F) := by
  simp [ratBasis, Module.Basis.localizationLocalization_apply]

theorem exists_trace_dual {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    [DecidableEq κ] (b : Module.Basis κ ℤ (𝓞 F)) :
    ∃ d : κ → F, ∀ v u, Algebra.trace ℚ F ((b v : F) * d u) = if v = u then 1 else 0 := by
  classical
  have hnd := traceForm_nondegenerate ℚ F
  refine ⟨fun u => (Algebra.traceForm ℚ F).dualBasis hnd (ratBasis b) u, fun v u => ?_⟩
  have h := LinearMap.BilinForm.apply_dualBasis_left (B := Algebra.traceForm ℚ F) hnd
    (ratBasis b) u v
  rw [Algebra.traceForm_apply, ratBasis_apply, mul_comm] at h
  exact h

theorem eq_of_trace_eq {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (b : Module.Basis κ ℤ (𝓞 F)) {x y : F}
    (h : ∀ v, Algebra.trace ℚ F ((b v : F) * x) = Algebra.trace ℚ F ((b v : F) * y)) :
    x = y := by
  have hnd := traceForm_nondegenerate ℚ F
  rw [← sub_eq_zero]
  apply hnd.2 _
  intro z
  have hL : (Algebra.trace ℚ F) ∘ₗ (LinearMap.mulRight ℚ (x - y)) = 0 := by
    refine (ratBasis b).ext fun v => ?_
    rw [LinearMap.comp_apply, LinearMap.mulRight_apply, ratBasis_apply, mul_sub, map_sub, h v,
      sub_self, LinearMap.zero_apply]
  exact LinearMap.congr_fun hL z

theorem exists_dual_param (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι]
    [DecidableEq ι] (B : Matrix ι ι F) (b : Module.Basis (InfinitePlace F) ℤ (𝓞 F)) (N : ℕ)
    (hB : B.det ≠ 0) (hN : 0 < N) :
    ∃ e : (ι × InfinitePlace F → ℤ) → ι → F,
      (∀ n i v, (N : ℚ) * Algebra.trace ℚ F ((b v : F) * (B *ᵥ e n) i) = n (i, v)) ∧
      ∀ y : ι → F, (∀ i v, ∃ m : ℤ,
        (N : ℚ) * Algebra.trace ℚ F ((b v : F) * (B *ᵥ y) i) = m) → ∃ n, e n = y := by
  classical
  obtain ⟨d, hd⟩ := exists_trace_dual b
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hu : IsUnit B.det := isUnit_iff_ne_zero.mpr hB
  have hBB : ∀ c : ι → F, B *ᵥ (B⁻¹ *ᵥ c) = c := fun c => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv B hu, Matrix.one_mulVec]
  have hinj : ∀ y : ι → F, B⁻¹ *ᵥ (B *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul B hu, Matrix.one_mulVec]
  obtain ⟨c, hc⟩ : ∃ c : (ι × InfinitePlace F → ℤ) → ι → F,
      ∀ n i v, (N : ℚ) * Algebra.trace ℚ F ((b v : F) * c n i) = n (i, v) := by
    refine ⟨fun n i => ∑ u, algebraMap ℚ F ((n (i, u) : ℚ) / N) * d u, fun n i v => ?_⟩
    have : Algebra.trace ℚ F ((b v : F) * ∑ u, algebraMap ℚ F ((n (i, u) : ℚ) / N) * d u)
        = (n (i, v) : ℚ) / N := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Finset.mul_sum, map_sum]
      have hterm : ∀ u, Algebra.trace ℚ F ((b v : F) * (algebraMap ℚ F ((n (i, u) : ℚ) / N) * d u))
          = ((n (i, u) : ℚ) / N) * (if v = u then 1 else 0) := by
        intro u
        rw [mul_left_comm, ← Algebra.smul_def, map_smul, hd, smul_eq_mul]
      rw [Finset.sum_congr rfl fun u _ => hterm u]
      simp
    simp only [this]
    field_simp
  refine ⟨fun n => B⁻¹ *ᵥ c n, fun n i v => ?_, fun y hy => ?_⟩
  · simp only [hBB]
    exact hc n i v
  · choose m hm using hy
    refine ⟨fun p => m p.1 p.2, ?_⟩
    have hcy : c (fun p => m p.1 p.2) = B *ᵥ y := by
      funext i
      exact eq_of_trace_eq b fun v =>
        mul_left_cancel₀ hNq ((hc (fun p => m p.1 p.2) i v).trans (hm i v).symm)
    change B⁻¹ *ᵥ c (fun p => m p.1 p.2) = y
    rw [hcy, hinj]

end GlobalTheory.CompanionTheory.SW.ThW.DualLattice
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DualLatticeParametrizationStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_lattice_parametrization : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι F) (b : Module.Basis (InfinitePlace F) ℤ (𝓞 F)) (N : ℕ), B.det ≠ 0 → 0 < N → ∃ e : (ι × InfinitePlace F → ℤ) → ι → F, (∀ n i v, (N : ℚ) * Algebra.trace ℚ F ((b v : F) * (B *ᵥ e n) i) = n (i, v)) ∧ ∀ y : ι → F, (∀ i v, ∃ m : ℤ, (N : ℚ) * Algebra.trace ℚ F ((b v : F) * (B *ᵥ y) i) = m) → ∃ n, e n = y := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThW.DualLattice.exists_dual_param | exact GlobalTheory.CompanionTheory.SW.ThW.DualLattice.exists_dual_param | (intros; apply GlobalTheory.CompanionTheory.SW.ThW.DualLattice.exists_dual_param <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WeilOrthogonalGroupInvariance
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WeilOrthogonalGroupInvariance
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Core.OrthMeas

theorem chiB_mulVec_mulVec {R : Type} [CommRing R] {ι : Type} [Fintype ι]
    (ψ : AddChar R ℂ) (B g : Matrix ι ι R) (hg : gᵀ * B * g = B) (x y : ι → R) :
    chiB ψ B (g *ᵥ x) (g *ᵥ y) = chiB ψ B x y := by
  have h : (g *ᵥ x) ⬝ᵥ (B *ᵥ (g *ᵥ y)) = x ⬝ᵥ (B *ᵥ y) := by
    conv_rhs => rw [← hg]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x gᵀ,
      Matrix.vecMul_transpose]
  simp only [chiB, h]

def mulVecEquiv {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (g : Matrix ι ι R) (hdet : IsUnit g.det) : (ι → R) ≃+ (ι → R) where
  toFun x := g *ᵥ x
  invFun x := g⁻¹ *ᵥ x
  left_inv x := by simp [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul g hdet]
  right_inv x := by simp [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv g hdet]
  map_add' := Matrix.mulVec_add g

theorem perp_image {V : Type} (χ : V → V → ℂ) (e : V ≃ V)
    (hχ : ∀ x y, χ (e x) (e y) = χ x y) (L : Set V) :
    perp χ (e '' L) = e '' perp χ L := by
  ext y
  constructor
  · intro hy
    refine ⟨e.symm y, fun x hx => ?_, e.apply_symm_apply y⟩
    have := hy (e x) ⟨x, hx, rfl⟩
    rwa [← e.apply_symm_apply y, hχ] at this
  · rintro ⟨z, hz, rfl⟩ x ⟨w, hw, rfl⟩
    rw [hχ]
    exact hz w hw

theorem map_eq_self {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]
    (χ : V → V → ℂ) (μ : Measure V) (hD : NADual V χ μ) (e : V ≃+ V) (he : Continuous e)
    (hes : Continuous e.symm) (hχ : ∀ x y, χ (e x) (e y) = χ x y) :
    Measure.map e μ = μ := by
  obtain ⟨hTG, hT2, hLC, hSC, hBS, hHaar, -, hEx, -, -, -, -, hPerp⟩ := hD
  haveI := hTG
  haveI := hT2
  haveI := hLC
  haveI := hSC
  haveI := hBS
  haveI := hHaar
  haveI : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ he hes
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, μ.map e = c • μ :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul (μ.map e) μ⟩
  let t : V ≃ₜ V := { toEquiv := e.toEquiv, continuous_toFun := he, continuous_invFun := hes }
  have key : ∀ A : Set V, IsOpen A → μ A = c * μ (e '' A) := by
    intro A hA
    have hm : MeasurableSet (e '' A) := (t.isOpenMap A hA).measurableSet
    have h1 : (μ.map e) (e '' A) = (c • μ) (e '' A) := by rw [hc]
    rw [Measure.map_apply he.measurable hm, Set.preimage_image_eq _ e.injective,
      Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h1
    exact h1
  obtain ⟨L, hLc, hLo, -⟩ := hEx 0
  have hset : ((L.map e.toAddMonoidHom : AddSubgroup V) : Set V) = e '' (L : Set V) := by
    ext x; simp
  have hL'c : IsCompact ((L.map e.toAddMonoidHom : AddSubgroup V) : Set V) := by
    rw [hset]; exact hLc.image he
  have hL'o : IsOpen ((L.map e.toAddMonoidHom : AddSubgroup V) : Set V) := by
    rw [hset]; exact t.isOpenMap _ hLo
  obtain ⟨-, hPo, -, hP⟩ := hPerp L hLc hLo
  obtain ⟨-, -, -, hP'⟩ := hPerp _ hL'c hL'o
  rw [hset, show perp χ (e '' (L : Set V)) = e '' perp χ (L : Set V) from
    perp_image χ e.toEquiv hχ _] at hP'
  have hcc : ((c : ℝ≥0∞)) * c = 1 := by
    rw [key _ hLo, key _ hPo] at hP
    calc ((c : ℝ≥0∞)) * c = (c : ℝ≥0∞) * c * (μ (e '' (L : Set V)) * μ (e '' perp χ (L : Set V))) := by
          rw [hP', mul_one]
      _ = 1 := by rw [← hP]; ring
  have hc1 : c = 1 := by
    have h2 : c * c = 1 := by exact_mod_cast hcc
    have h3 : c ^ 2 = 1 := by rw [sq]; exact h2
    exact (pow_eq_one_iff.1 h3).resolve_right two_ne_zero
  rw [hc, hc1, one_smul]

theorem orth_meas : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [MeasurableSpace R] (ι : Type)
    [Fintype ι] [DecidableEq ι] (ψ : AddChar R ℂ) (h : R) (B : Matrix ι ι R) (μ : Measure (ι → R)),
    NAQuad ψ h B μ → ∀ g : Matrix ι ι R, IsUnit g.det → gᵀ * B * g = B →
      Measure.map (fun x => g *ᵥ x) μ = μ ∧ ∀ φ : (ι → R) → ℂ, SB φ →
        SB (fun x => φ (g *ᵥ x)) ∧
          ∀ y, fou (chiB ψ B) μ (fun x => φ (g *ᵥ x)) y = fou (chiB ψ B) μ φ (g *ᵥ y) := by
  intro R _ _ _ ι _ _ ψ h B μ hQ g hdet hg
  obtain ⟨hTR, -, -, -, -, hD⟩ := hQ
  haveI := hTR
  have hBS : BorelSpace (ι → R) := hD.2.2.2.2.1
  have he : Continuous (mulVecEquiv g hdet) :=
    Continuous.matrix_mulVec continuous_const continuous_id
  have hes : Continuous (mulVecEquiv g hdet).symm :=
    Continuous.matrix_mulVec continuous_const continuous_id
  have hχ : ∀ x y, chiB ψ B (mulVecEquiv g hdet x) (mulVecEquiv g hdet y) = chiB ψ B x y :=
    chiB_mulVec_mulVec ψ B g hg
  have hmap : Measure.map (fun x => g *ᵥ x) μ = μ :=
    map_eq_self (chiB ψ B) μ hD (mulVecEquiv g hdet) he hes hχ
  let t : (ι → R) ≃ₜ (ι → R) :=
    { toEquiv := (mulVecEquiv g hdet).toEquiv, continuous_toFun := he, continuous_invFun := hes }
  refine ⟨hmap, fun φ hφ => ⟨⟨hφ.1.comp_continuous he, hφ.2.comp_homeomorph t⟩, fun y => ?_⟩⟩
  have hI := t.measurableEmbedding.integral_map (μ := μ) (fun x => φ x * chiB ψ B x (g *ᵥ y))
  have ht : (⇑t : (ι → R) → (ι → R)) = fun x => g *ᵥ x := rfl
  rw [ht, hmap] at hI
  simp only [fou]
  rw [hI]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [chiB_mulVec_mulVec ψ B g hg]

end GlobalTheory.CompanionTheory.SW.Core.OrthMeas
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WeilOrthogonalGroupInvarianceStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_orthogonal_group_invariance : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [MeasurableSpace R] (ι : Type) [Fintype ι] [DecidableEq ι] (ψ : AddChar R ℂ) (h : R) (B : Matrix ι ι R) (μ : Measure (ι → R)), NAQuad ψ h B μ → ∀ g : Matrix ι ι R, IsUnit g.det → gᵀ * B * g = B → Measure.map (fun x => g *ᵥ x) μ = μ ∧ ∀ φ : (ι → R) → ℂ, SB φ → SB (fun x => φ (g *ᵥ x)) ∧ ∀ y, fou (chiB ψ B) μ (fun x => φ (g *ᵥ x)) y = fou (chiB ψ B) μ φ (g *ᵥ y) := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core.OrthMeas.orth_meas | exact GlobalTheory.CompanionTheory.SW.Core.OrthMeas.orth_meas | (intros; apply GlobalTheory.CompanionTheory.SW.Core.OrthMeas.orth_meas <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FourierTransformLatticeIndicator
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FourierTransformLatticeIndicator
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.Core

theorem fou_indicator_coset :
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (χ : V → V → ℂ) (μ : Measure V),
      NADual V χ μ → ∀ L : AddSubgroup V, IsCompact (L : Set V) → IsOpen (L : Set V) → ∀ a y : V,
        fou χ μ (Set.indicator {x | x - a ∈ L} (fun _ => (1 : ℂ))) y =
          ((μ L).toReal : ℂ) * χ a y * Set.indicator (perp χ L) (fun _ => (1 : ℂ)) y := by
  intro V _ _ _ χ μ h L _ hLo a y
  obtain ⟨hTG, _, _, hSC, hB, hH, _, _, _, _, _, hadd, _⟩ := h
  have hLm : MeasurableSet (L : Set V) := hLo.measurableSet

  have key : ∫ x, Set.indicator (L : Set V) (fun _ => (1 : ℂ)) x * χ x y ∂μ =
      ((μ L).toReal : ℂ) * Set.indicator (perp χ L) (fun _ => (1 : ℂ)) y := by
    by_cases hy : y ∈ perp χ L
    · have h1 : (fun x => Set.indicator (L : Set V) (fun _ => (1 : ℂ)) x * χ x y) =
          fun x => Set.indicator (L : Set V) (fun _ => (1 : ℂ)) x := by
        funext x
        by_cases hx : x ∈ (L : Set V)
        · simp [Set.indicator_of_mem hx, hy x hx]
        · simp [Set.indicator_of_notMem hx]
      rw [h1, integral_indicator_const _ hLm, Set.indicator_of_mem hy]
      simp [Measure.real]
    · obtain ⟨l, hl, hne⟩ : ∃ l ∈ (L : Set V), χ l y ≠ 1 := by
        simpa [perp] using hy
      set J := ∫ x, Set.indicator (L : Set V) (fun _ => (1 : ℂ)) x * χ x y ∂μ with hJ
      have hshift : J = χ l y * J := by
        have h2 := integral_add_right_eq_self (μ := μ)
          (fun x => Set.indicator (L : Set V) (fun _ => (1 : ℂ)) x * χ x y) l
        refine h2.symm.trans ?_
        rw [hJ, ← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        have hmem : x + l ∈ (L : Set V) ↔ x ∈ (L : Set V) := L.add_mem_cancel_right hl
        by_cases hx : x ∈ (L : Set V)
        · simp only [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.2 hx), hadd]
          ring
        · simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (hmem.1 h))]
      have hJ0 : J = 0 := by
        have h3 : (1 - χ l y) * J = 0 := by
          rw [sub_mul, one_mul, ← hshift, sub_self]
        rcases mul_eq_zero.1 h3 with h4 | h4
        · exact absurd (sub_eq_zero.1 h4).symm hne
        · exact h4
      rw [hJ0, Set.indicator_of_notMem hy, mul_zero]

  unfold fou
  have h5 := integral_add_right_eq_self (μ := μ)
    (fun x => Set.indicator {x | x - a ∈ L} (fun _ => (1 : ℂ)) x * χ x y) a
  rw [← h5]
  have h6 : (fun x => Set.indicator {x | x - a ∈ L} (fun _ => (1 : ℂ)) (x + a) * χ (x + a) y) =
      fun x => χ a y * (Set.indicator (L : Set V) (fun _ => (1 : ℂ)) x * χ x y) := by
    funext x
    have hmem : x + a ∈ {x | x - a ∈ L} ↔ x ∈ (L : Set V) := by simp
    by_cases hx : x ∈ (L : Set V)
    · simp only [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.2 hx), hadd]
      ring
    · simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (hmem.1 h))]
  rw [h6, integral_const_mul, key]
  ring

end GlobalTheory.CompanionTheory.SW.Core
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FourierTransformLatticeIndicatorStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_transform_lattice_indicator : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (χ : V → V → ℂ) (μ : Measure V), NADual V χ μ → ∀ L : AddSubgroup V, IsCompact (L : Set V) → IsOpen (L : Set V) → ∀ a y : V, fou χ μ (Set.indicator {x | x - a ∈ L} (fun _ => (1 : ℂ))) y = ((μ L).toReal : ℂ) * χ a y * Set.indicator (perp χ L) (fun _ => (1 : ℂ)) y := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core.fou_indicator_coset | exact GlobalTheory.CompanionTheory.SW.Core.fou_indicator_coset | (intros; apply GlobalTheory.CompanionTheory.SW.Core.fou_indicator_coset <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaFunctionAutomorphy
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ThW

section Linear

theorem sb_add {V : Type} [TopologicalSpace V] {φ φ' : V → ℂ} (h : SB φ) (h' : SB φ') : SB (φ + φ') :=
  ⟨h.1.add h'.1, h.2.add h'.2⟩

theorem sb_smul {V : Type} [TopologicalSpace V] (c : ℂ) {φ : V → ℂ} (h : SB φ) : SB (c • φ) :=
  ⟨by
    have := h.1.comp (fun z => c * z)
    exact this, h.2.smul_left⟩

theorem sb_integrable {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]
    {χ : V → V → ℂ} {μ : Measure V} (hV : NADual V χ μ) {φ : V → ℂ} (h : SB φ) (y : V) :
    Integrable (fun x => φ x * χ x y) μ := by
  obtain ⟨hT, _, _, _, hB, hH, _, _, hC, _⟩ := hV
  have hc : Continuous fun x => φ x * χ x y :=
    h.1.continuous.mul (hC.comp (by fun_prop : Continuous fun x : V => (x, y)))
  exact hc.integrable_of_hasCompactSupport h.2.mul_right

theorem fou_add {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]
    {χ : V → V → ℂ} {μ : Measure V} (hV : NADual V χ μ) {φ φ' : V → ℂ} (h : SB φ) (h' : SB φ') :
    fou χ μ (φ + φ') = fou χ μ φ + fou χ μ φ' := by
  funext y
  simp only [fou, Pi.add_apply, add_mul]
  exact integral_add (sb_integrable hV h y) (sb_integrable hV h' y)

theorem fou_smul {V : Type} [MeasurableSpace V] (χ : V → V → ℂ) (μ : Measure V) (c : ℂ)
    (φ : V → ℂ) : fou χ μ (c • φ) = c • fou χ μ φ := by
  funext y
  simp only [fou, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul c _

end Linear

section Global

variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem thTerm_one (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ))
    (P : InfinitePlace F → Matrix ι ι ℝ) (φ : (ι → A F) → ℂ) (τ : InfinitePlace F → ℂ) (x : ι → F) :
    thTerm B ρ P 1 (fun _ => 1) φ τ x = φ (toA x) * gauss B ρ P τ (cur (emb ρ x)) := by
  simp only [thTerm, one_mulVec]
  rfl

theorem theta_add {B : Matrix ι ι F} {ρ : InfinitePlace F → (F →+* ℝ)}
    {P : InfinitePlace F → Matrix ι ι ℝ} {τ : InfinitePlace F → ℂ} {φ φ' : (ι → A F) → ℂ}
    (h : Summable fun x => ‖thTerm B ρ P 1 (fun _ => 1) φ τ x‖)
    (h' : Summable fun x => ‖thTerm B ρ P 1 (fun _ => 1) φ' τ x‖) :
    theta B ρ P 1 (fun _ => 1) (φ + φ') τ =
      theta B ρ P 1 (fun _ => 1) φ τ + theta B ρ P 1 (fun _ => 1) φ' τ := by
  unfold theta
  rw [← h.of_norm.tsum_add h'.of_norm]
  refine tsum_congr fun x => ?_
  simp only [thTerm, Pi.add_apply, add_mul]

theorem theta_smul (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ))
    (P : InfinitePlace F → Matrix ι ι ℝ) (τ : InfinitePlace F → ℂ) (c : ℂ) (φ : (ι → A F) → ℂ) :
    theta B ρ P 1 (fun _ => 1) (c • φ) τ = c * theta B ρ P 1 (fun _ => 1) φ τ := by
  unfold theta
  rw [← tsum_mul_left]
  refine tsum_congr fun x => ?_
  simp only [thTerm, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem orth_one (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) :
    IsOrth B ρ 1 (fun _ => 1) := by
  simp [IsOrth]

theorem poisson_form [DecidableEq (InfinitePlace F)] {M : ℕ} {B : Matrix ι ι F}
    {ρ : InfinitePlace F → (F →+* ℝ)} {P : InfinitePlace F → Matrix ι ι ℝ} (hQ : QSetup M B ρ P)
    {τ : InfinitePlace F → ℂ} (hτ : ∀ w, 0 < (τ w).im)
    (g : Matrix (ι × InfinitePlace F) (ι × InfinitePlace F) ℝ) (hg : g.det ≠ 0)
    (a : ι × InfinitePlace F → ℝ) (u : (ι × InfinitePlace F → ℤ) → ι × InfinitePlace F → ℝ)
    (hu : ∀ n, DM B ρ *ᵥ u n = (g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) :
    ∑' n : ι × InfinitePlace F → ℤ, gauss B ρ P τ (cur (a + g *ᵥ fun i => (n i : ℝ))) =
      ((|g.det|⁻¹ * (Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)|)⁻¹ : ℝ) : ℂ) * cG B ρ P τ *
        ∑' n : ι × InfinitePlace F → ℤ, gauss B ρ P (fun w => -(τ w)⁻¹) (cur (u n)) *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((a ⬝ᵥ (DM B ρ *ᵥ u n) : ℝ) : ℂ)) := by
  obtain ⟨hS, hP, hE⟩ := GlobalTheory.T.siegel_matrix_symmetric_posdef_imag F ι M B ρ P hQ τ hτ
  have hpl := GlobalTheory.T.poisson_summation_gaussian (ι × InfinitePlace F) (ZM B ρ P τ) hS hP g hg a
  dsimp only at hpl
  obtain ⟨-, -, h⟩ := hpl
  simp only [hE] at h
  have hs : ((Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)| : ℝ) : ℂ) ≠ 0 := by
    have h0 : ((Algebra.norm ℚ B.det : ℚ) : ℝ) ≠ 0 := by
      exact_mod_cast (Algebra.norm_ne_zero_iff.mpr hQ.2.2.2.1)
    have : 0 < Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)| :=
      Real.sqrt_pos.mpr (abs_pos.mpr h0)
    exact_mod_cast this.ne'
  have key : ∀ n : ι × InfinitePlace F → ℤ,
      (∫ x : ι × InfinitePlace F → ℝ, gauss B ρ P τ (cur x) * Complex.exp (2 * (Real.pi : ℂ) *
          Complex.I * ((x ⬝ᵥ ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) : ℝ) : ℂ))) *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) *
          ((a ⬝ᵥ ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) : ℝ) : ℂ)) =
      (((Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)| : ℝ) : ℂ)⁻¹ * cG B ρ P τ) *
        (gauss B ρ P (fun w => -(τ w)⁻¹) (cur (u n)) *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((a ⬝ᵥ (DM B ρ *ᵥ u n) : ℝ) : ℂ))) := by
    intro n
    have hf := GlobalTheory.T.gaussian_fourier_transform_formula F ι M B ρ P hQ τ hτ (u n)
    rw [hu n] at hf
    rw [hu n, mul_assoc (_)⁻¹, ← mul_assoc (cG B ρ P τ), ← hf]
    field_simp
  rw [h, tsum_congr key, tsum_mul_left]
  push_cast
  ring

end Global

section Base

variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem theta_indC [DecidableEq (InfinitePlace F)] (B : Matrix ι ι F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ)
    (τ : InfinitePlace F → ℂ) (a : ι → F) (N : ℕ) (g : Matrix (ι × InfinitePlace F) (ι × InfinitePlace F) ℝ)
    (e : (ι × InfinitePlace F → ℤ) → ι → F) (hi : Function.Injective e)
    (hr : ∀ x : ι → F, toA x - toA a ∈ latN F ι N ↔ x ∈ Set.range e)
    (he : ∀ n, emb ρ (e n) = emb ρ a + g *ᵥ fun p => (n p : ℝ)) :
    theta B ρ P 1 (fun _ => 1) (indC N a) τ =
      ∑' n : ι × InfinitePlace F → ℤ, gauss B ρ P τ (cur (emb ρ a + g *ᵥ fun i => (n i : ℝ))) := by
  unfold theta
  rw [← hi.tsum_eq]
  · refine tsum_congr fun n => ?_
    rw [thTerm_one, he n, indC, Set.indicator_of_mem, one_mul]
    exact (hr _).2 ⟨n, rfl⟩
  · intro x hx
    by_contra hc
    apply hx
    rw [thTerm_one, indC, Set.indicator_of_notMem, zero_mul]
    exact fun h => hc ((hr x).1 h)

theorem base [MeasurableSpace (A F)] [BorelSpace (A F)] {lf : Measure (A F)}
    (hl : lf.IsAddHaarMeasure) (h1 : lf (Oh F) = 1) {ψ : AddChar (A F) ℂ} (hψ : IsStdChar F ψ)
    {M : ℕ} {B : Matrix ι ι F} {ρ : InfinitePlace F → (F →+* ℝ)}
    {P : InfinitePlace F → Matrix ι ι ℝ} (hQ : QSetup M B ρ P)
    (hV : NADual (ι → A F) (chiB ψ (Bf B)) (muF B lf)) (a : ι → F) {N : ℕ} (hN : 0 < N)
    {τ : InfinitePlace F → ℂ} (hτ : ∀ w, 0 < (τ w).im) :
    cG B ρ P τ * theta B ρ P 1 (fun _ => 1) (fou (chiB ψ (Bf B)) (muF B lf) (indC N a))
      (fun w => -(τ w)⁻¹) = theta B ρ P 1 (fun _ => 1) (indC N a) τ := by
  classical
  obtain ⟨hT, -, -, hdet, hemb, -, -⟩ := id hQ
  obtain ⟨b⟩ := GlobalTheory.T.totally_real_integral_basis_exists F hT
  have hgd := GlobalTheory.T.lattice_matrix_determinant_formula F ι ρ hT hemb b N
  set g := gM (ι := ι) ρ (fun v => b v) N with hgdef
  have hdisc : 0 < Real.sqrt |(discr F : ℝ)| :=
    Real.sqrt_pos.mpr (abs_pos.mpr (by exact_mod_cast discr_ne_zero F))
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hg : g.det ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hgd
    exact (pow_pos (mul_pos (pow_pos hNr _) hdisc) _).ne hgd
  obtain ⟨e, ei, er, ee⟩ := GlobalTheory.T.lattice_coset_parametrization F ι ρ b a N hN
  obtain ⟨e', he', es⟩ := GlobalTheory.T.dual_lattice_parametrization F ι B b N hdet hN
  have hu : ∀ n : ι × InfinitePlace F → ℤ, DM B ρ *ᵥ emb ρ (e' n) = (g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ) := by
    intro n
    have h2 := GlobalTheory.T.gram_transpose_dual_trace_identity F ι M B ρ P hQ (fun v => b v) N (e' n)
    have h3 : gᵀ *ᵥ (DM B ρ *ᵥ emb ρ (e' n)) = fun i => (n i : ℝ) := by
      rw [hgdef, h2]
      funext p
      have := he' n p.1 p.2
      rw [this]
      simp
    have hU : IsUnit g.det := isUnit_iff_ne_zero.mpr hg
    rw [← h3, mulVec_mulVec, ← transpose_mul, mul_nonsing_inv _ hU, transpose_one, one_mulVec]
  have pf := poisson_form hQ hτ g hg (emb ρ a) (fun n => emb ρ (e' n)) hu
  have ei' : Function.Injective e' := by
    intro n n' h
    funext p
    have h3 := he' n p.1 p.2
    rw [h, he' n' p.1 p.2] at h3
    exact_mod_cast h3.symm
  have hfou : ∀ y : ι → F, fou (chiB ψ (Bf B)) (muF B lf) (indC N a) (toA y) =
      ((muF B lf (latN F ι N : Set (ι → A F))).toReal : ℂ) * chiB ψ (Bf B) (toA a) (toA y) *
        Set.indicator (perp (chiB ψ (Bf B)) (latN F ι N : Set (ι → A F))) (fun _ => (1 : ℂ)) (toA y) :=
    fun y => GlobalTheory.T.fourier_transform_lattice_indicator _ _ _ hV (latN F ι N) (GlobalTheory.T.adelic_level_lattice_compact_open F ι N hN).1 (GlobalTheory.T.adelic_level_lattice_compact_open F ι N hN).2.1 (toA a) (toA y)
  have hperp : ∀ y : ι → F, toA y ∈ perp (chiB ψ (Bf B)) (latN F ι N : Set (ι → A F)) ↔
      y ∈ Set.range e' := by
    intro y
    rw [GlobalTheory.T.dual_lattice_membership_trace F ψ hψ ι B b N hN y]
    constructor
    · intro h
      exact es y h
    · rintro ⟨n, rfl⟩ i v
      exact ⟨n (i, v), he' n i v⟩
  have hL : theta B ρ P 1 (fun _ => 1) (fou (chiB ψ (Bf B)) (muF B lf) (indC N a))
      (fun w => -(τ w)⁻¹) = ((muF B lf (latN F ι N : Set (ι → A F))).toReal : ℂ) *
        ∑' n : ι × InfinitePlace F → ℤ, gauss B ρ P (fun w => -(τ w)⁻¹) (cur (emb ρ (e' n))) *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) *
            ((emb ρ a ⬝ᵥ (DM B ρ *ᵥ emb ρ (e' n)) : ℝ) : ℂ)) := by
    unfold theta
    rw [← ei'.tsum_eq, ← tsum_mul_left]
    · refine tsum_congr fun n => ?_
      rw [thTerm_one, hfou, Set.indicator_of_mem ((hperp _).2 ⟨n, rfl⟩),
        GlobalTheory.T.adelic_character_exponential_formula F ψ hψ ι M B ρ P hQ a (e' n)]
      ring
    · intro x hx
      by_contra hc
      apply hx
      rw [thTerm_one, hfou, Set.indicator_of_notMem (fun h => hc ((hperp x).1 h))]
      simp
  have hmass := GlobalTheory.T.adelic_lattice_measure_formula F lf hl h1 ι B N hN
  rw [hL, theta_indC B ρ P τ a N g e ei er ee, pf, hmass, hgd]
  have hk : kap F = (Real.sqrt |(discr F : ℝ)|)⁻¹ := rfl
  rw [hk]
  push_cast
  simp only [mul_inv, mul_pow, inv_pow]
  ring

theorem core [MeasurableSpace (A F)] [BorelSpace (A F)] {lf : Measure (A F)}
    (hl : lf.IsAddHaarMeasure) (h1 : lf (Oh F) = 1) {ψ : AddChar (A F) ℂ} (hψ : IsStdChar F ψ)
    {M : ℕ} {B : Matrix ι ι F} {ρ : InfinitePlace F → (F →+* ℝ)}
    {P : InfinitePlace F → Matrix ι ι ℝ} (hQ : QSetup M B ρ P)
    (hV : NADual (ι → A F) (chiB ψ (Bf B)) (muF B lf)) {φ : (ι → A F) → ℂ} (hφ : SB φ)
    {τ : InfinitePlace F → ℂ} (hτ : ∀ w, 0 < (τ w).im) :
    cG B ρ P τ * theta B ρ P 1 (fun _ => 1) (fou (chiB ψ (Bf B)) (muF B lf) φ)
      (fun w => -(τ w)⁻¹) = theta B ρ P 1 (fun _ => 1) φ τ := by
  have hτ' : ∀ w, 0 < (-(τ w)⁻¹).im := by
    intro w
    have h0 : τ w ≠ 0 := fun h => by simpa [h] using hτ w
    simp only [Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
    exact div_pos (hτ w) (Complex.normSq_pos.mpr h0)
  have hsum : ∀ {σ : InfinitePlace F → ℂ}, (∀ w, 0 < (σ w).im) → ∀ {f : (ι → A F) → ℂ}, SB f →
      Summable fun x => ‖thTerm B ρ P 1 (fun _ => 1) f σ x‖ := fun hσ _ hf =>
    (GlobalTheory.T.theta_series_summable F ι M B ρ P hQ 1 (fun _ => 1) (orth_one B ρ) _ hσ).1 _ hf
  have hsb : ∀ {f : (ι → A F) → ℂ}, SB f → SB (fou (chiB ψ (Bf B)) (muF B lf) f) := fun hf =>
    (GlobalTheory.T.fourier_inversion_schwartz_bruhat _ _ _ hV _ hf).1
  obtain ⟨N, hN, s, c, rfl⟩ := GlobalTheory.T.schwartz_bruhat_span_indicators F ι _ _ hV (fun N hN => (GlobalTheory.T.adelic_level_lattice_compact_open F ι N hN).2.1) φ hφ
  have hI : ∀ a : ι → F, SB (indC N a) := (GlobalTheory.T.adelic_level_lattice_compact_open F ι N hN).2.2
  classical
  have main : ∀ t : Finset (ι → F), SB (∑ a ∈ t, c a • indC N a) ∧
      cG B ρ P τ * theta B ρ P 1 (fun _ => 1)
        (fou (chiB ψ (Bf B)) (muF B lf) (∑ a ∈ t, c a • indC N a)) (fun w => -(τ w)⁻¹) =
      theta B ρ P 1 (fun _ => 1) (∑ a ∈ t, c a • indC N a) τ := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      have h0 : SB (0 : (ι → A F) → ℂ) := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
      have hf0 : fou (chiB ψ (Bf B)) (muF B lf) (0 : (ι → A F) → ℂ) = 0 := by
        funext y
        simp [fou]
      have ht0 : ∀ σ, theta B ρ P 1 (fun _ => 1) (0 : (ι → A F) → ℂ) σ = 0 := by
        intro σ
        simp [theta, thTerm]
      simp only [Finset.sum_empty]
      exact ⟨h0, by rw [hf0, ht0, ht0, mul_zero]⟩
    | insert a t ha ih =>
      obtain ⟨ihs, ihe⟩ := ih
      have hca := sb_smul (c a) (hI a)
      simp only [Finset.sum_insert ha]
      refine ⟨sb_add hca ihs, ?_⟩
      rw [fou_add hV hca ihs, theta_add (hsum hτ' (hsb hca)) (hsum hτ' (hsb ihs)),
        theta_add (hsum hτ hca) (hsum hτ ihs), mul_add, ihe, fou_smul, theta_smul, theta_smul]
      congr 1
      rw [← base hl h1 hψ hQ hV a hN hτ]
      ring
  exact (main s).2

theorem thetaInvariance : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ (gf : Matrix ι ι (A F)) (gi : InfinitePlace F → Matrix ι ι ℝ), IsOrth B ρ gf gi → ∀ φ : (ι → A F) → ℂ, SB φ → ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → cG B ρ P τ * theta B ρ P gf gi (fou (chiB ψ (Bf B)) (muF B lf) φ) (fun w => -(τ w)⁻¹) = theta B ρ P gf gi φ τ := by
  intro F _ _ _ _ lf hl h1 ψ hψ ι _ _ M B ρ P hQ gf gi hO φ hφ τ hτ
  obtain ⟨-, -, hsym, hdet, -, -, -⟩ := id hQ
  have hNA := GlobalTheory.T.weil_representation_quadratic_datum F lf hl h1 ψ hψ ι B hsym hdet
  have hV := hNA.2.2.2.2.2
  have hBu : IsUnit (Bf B).det := by
    have : (Bf B).det = algebraMap F (A F) B.det := by
      rw [Bf, RingHom.map_det]
      rfl
    rw [this]
    exact (isUnit_iff_ne_zero.mpr hdet).map _
  have hgu : IsUnit gf.det := by
    have h := congrArg det hO.1
    rw [det_mul, det_mul, det_transpose] at h
    have h2 : gf.det * gf.det = 1 := by
      apply hBu.mul_right_cancel
      linear_combination h
    exact IsUnit.of_mul_eq_one _ h2
  obtain ⟨-, hfou⟩ := GlobalTheory.T.weil_orthogonal_group_invariance (A F) ι ψ (hf F) (Bf B) (muF B lf) hNA gf hgu hO.1
  obtain ⟨hsb, hfy⟩ := hfou φ hφ
  have hQ' := GlobalTheory.T.quadratic_setup_invariant_under_isometry F ι M B ρ P gi hQ hO.2
  obtain ⟨hga, hgc⟩ := GlobalTheory.T.gaussian_change_of_variables_isometry F ι B ρ P gi hdet hO.2
  have hth : ∀ (f : (ι → A F) → ℂ) (σ : InfinitePlace F → ℂ), theta B ρ P gf gi f σ =
      theta B ρ (fun w => (gi w)ᵀ * P w * gi w) 1 (fun _ => 1) (fun x => f (gf *ᵥ x)) σ := by
    intro f σ
    refine tsum_congr fun x => ?_
    rw [thTerm_one]
    simp only [thTerm]
    rw [hga]
    rfl
  have hc := core hl h1 hψ hQ' hV hsb hτ
  rw [hth, hth, ← hc, hgc]
  congr 2
  funext y
  exact (hfy _).symm

end Base

end GlobalTheory.CompanionTheory.SW.ThW
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaFunctionAutomorphyStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_function_automorphy : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ (gf : Matrix ι ι (A F)) (gi : InfinitePlace F → Matrix ι ι ℝ), IsOrth B ρ gf gi → ∀ φ : (ι → A F) → ℂ, SB φ → ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → cG B ρ P τ * theta B ρ P gf gi (fou (chiB ψ (Bf B)) (muF B lf) φ) (fun w => -(τ w)⁻¹) = theta B ρ P gf gi φ τ := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThW.thetaInvariance | exact GlobalTheory.CompanionTheory.SW.ThW.thetaInvariance | (intros; apply GlobalTheory.CompanionTheory.SW.ThW.thetaInvariance <;> assumption)
end
