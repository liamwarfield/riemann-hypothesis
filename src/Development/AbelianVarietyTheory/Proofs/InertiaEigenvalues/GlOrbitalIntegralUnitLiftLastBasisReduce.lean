module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormMulApplyLeOne
open GlobalTheory.JR Matrix

noncomputable section

namespace GlobalTheory.JR.GLift

theorem norm_mul_apply_le_one {F : Type} [NormedField F] [IsUltrametricDist F] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) F) (hA : ∀ i j, ‖A i j‖ ≤ 1) (hB : ∀ i j, ‖B i j‖ ≤ 1) (i j : Fin n) :
    ‖(A * B) i j‖ ≤ 1 := by
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hA i k) (norm_nonneg _) (hB k j)

theorem norm_one_apply_le_one {F : Type} [NormedField F] {n : ℕ} (i j : Fin n) :
    ‖(1 : Matrix (Fin n) (Fin n) F) i j‖ ≤ 1 := by
  rw [Matrix.one_apply]
  split_ifs <;> simp

def glOSub (n : ℕ) (F : Type) [NormedField F] [IsUltrametricDist F] : Subgroup (GL (Fin n) F) where
  carrier := glO n F
  mul_mem' {a b} ha hb := by
    intro i j
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]
      exact norm_mul_apply_le_one _ _ (fun i j => (ha i j).1) (fun i j => (hb i j).1) i j
    · rw [_root_.mul_inv_rev, Units.val_mul]
      exact norm_mul_apply_le_one _ _ (fun i j => (hb i j).2) (fun i j => (ha i j).2) i j
  one_mem' := by
    intro i j
    simp only [inv_one, Units.val_one]
    exact ⟨norm_one_apply_le_one i j, norm_one_apply_le_one i j⟩
  inv_mem' {a} ha := by
    intro i j
    rw [inv_inv]
    exact ⟨(ha i j).2, (ha i j).1⟩

theorem coe_glOSub (n : ℕ) (F : Type) [NormedField F] [IsUltrametricDist F] :
    (glOSub n F : Set (GL (Fin n) F)) = glO n F := rfl

end GlobalTheory.JR.GLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasCompactSupportJacquetRallisOrbitalIntegrand
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasCompactSupportJacquetRallisOrbitalIntegrand
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.GLCompact

theorem Bm_act {k : Type} [CommRing k] {r : ℕ} (g : GL (Fin r) k) (Y : Gl r k) :
    Bm (act g Y) = (g : Matrix (Fin r) (Fin r) k) * Bm Y := by
  have hcol : ∀ j : ℕ, ((act g Y).1 ^ j) *ᵥ (act g Y).2.1 =
      (g : Matrix (Fin r) (Fin r) k) *ᵥ ((Y.1 ^ j) *ᵥ Y.2.1) := by
    intro j
    simp only [act]
    rw [Units.conj_pow, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc,
      Units.inv_mul, Matrix.mul_one]
  ext i j
  simp only [Bm, Matrix.of_apply, Matrix.mul_apply, hcol]
  simp [Matrix.mulVec, dotProduct]

theorem continuous_Bm {k : Type} [NormedField k] {r : ℕ} : Continuous (fun Y : Gl r k => Bm Y) := by
  refine continuous_matrix fun i j => ?_
  simp only [Bm, Matrix.of_apply]
  exact (continuous_apply i).comp
    ((continuous_fst.pow (j : ℕ)).matrix_mulVec (continuous_fst.comp continuous_snd))

theorem continuous_Cm {k : Type} [NormedField k] {r : ℕ} : Continuous (fun Y : Gl r k => Cm Y) := by
  refine continuous_matrix fun i j => ?_
  simp only [Cm, Matrix.of_apply]
  exact (continuous_apply j).comp
    (((continuous_fst.comp (continuous_snd.comp continuous_snd))).matrix_vecMul
      (continuous_fst.pow (i : ℕ)))

end GlobalTheory.JR.GLCompact

private theorem isCompact_unit_box (F : Type) [NontriviallyNormedField F] [ProperSpace F] (n : ℕ) :
    IsCompact {Z : Gl n F | (∀ i j, ‖Z.1 i j‖ ≤ 1) ∧ (∀ i, ‖Z.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Z.2.2.1 i‖ ≤ 1) ∧
      ‖Z.2.2.2‖ ≤ 1} := by
  have hv : IsCompact (Set.univ.pi fun _ : Fin n => Metric.closedBall (0 : F) 1) :=
    isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  have hm : IsCompact {A : Matrix (Fin n) (Fin n) F | ∀ i j, ‖A i j‖ ≤ 1} := by
    have h : {A : Matrix (Fin n) (Fin n) F | ∀ i j, ‖A i j‖ ≤ 1} =
        Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => Metric.closedBall (0 : F) 1 := by
      ext A
      exact ⟨fun h i _ j _ => by simpa using h i j,
        fun h i j => by simpa using h i (Set.mem_univ i) j (Set.mem_univ j)⟩
    rw [h]
    exact isCompact_univ_pi fun _ => hv
  have h : {Z : Gl n F | (∀ i j, ‖Z.1 i j‖ ≤ 1) ∧ (∀ i, ‖Z.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Z.2.2.1 i‖ ≤ 1) ∧
      ‖Z.2.2.2‖ ≤ 1} = {A : Matrix (Fin n) (Fin n) F | ∀ i j, ‖A i j‖ ≤ 1} ×ˢ
        ((Set.univ.pi fun _ : Fin n => Metric.closedBall (0 : F) 1) ×ˢ
          ((Set.univ.pi fun _ : Fin n => Metric.closedBall (0 : F) 1) ×ˢ Metric.closedBall (0 : F) 1)) := by
    ext Z; simp
  rw [h]
  exact hm.prod (hv.prod (hv.prod (isCompact_closedBall 0 1)))

theorem GlobalTheory.JR.orbG_integrand_hasCompactSupport : ∀ (F : Type) [NontriviallyNormedField F] [LocallyCompactSpace F] (n : ℕ) (Y : Gl n F), Delta (inv Y) ≠ 0 → HasCompactSupport (fun g : GL (Fin n) F => unitG n F (act g Y) * omega (act g Y)) := by
  intro F _ _ n Y hY
  have : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  obtain ⟨-, -, hCB, -, -⟩ := GlobalTheory.T.jacquetRallis_borderedMatrix_normalForm_invariants F n
  have hdet : (Cm Y).det * (Bm Y).det ≠ 0 := by
    rw [← Matrix.det_mul, hCB Y]
    exact hY
  have hB : IsUnit (Bm Y).det := isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul hdet)
  have hC : IsUnit (Cm Y).det := isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul hdet)

  have hψ : Continuous (fun Z : Gl n F =>
      (Bm Z * (Bm Y)⁻¹, MulOpposite.op ((Cm Y)⁻¹ * Cm Z))) :=
    (GlobalTheory.JR.GLCompact.continuous_Bm.matrix_mul continuous_const).prodMk
      (MulOpposite.continuous_op.comp (continuous_const.matrix_mul GlobalTheory.JR.GLCompact.continuous_Cm))
  have hK := Units.isClosedEmbedding_embedProduct.isCompact_preimage
    ((isCompact_unit_box F n).image hψ)
  refine HasCompactSupport.intro hK ?_
  intro g hg
  have hgY : act g Y ∉ {Z : Gl n F | (∀ i j, ‖Z.1 i j‖ ≤ 1) ∧ (∀ i, ‖Z.2.1 i‖ ≤ 1) ∧
      (∀ i, ‖Z.2.2.1 i‖ ≤ 1) ∧ ‖Z.2.2.2‖ ≤ 1} := by
    intro hmem
    refine hg ⟨act g Y, hmem, Prod.ext ?_ ?_⟩
    · show Bm (act g Y) * (Bm Y)⁻¹ = (g : Matrix (Fin n) (Fin n) F)
      rw [GlobalTheory.JR.GLCompact.Bm_act, Matrix.mul_nonsing_inv_cancel_right _ _ hB]
    · show MulOpposite.op ((Cm Y)⁻¹ * Cm (act g Y)) =
        MulOpposite.op ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
      rw [GlobalTheory.JR.TransferFactor.Cm_act, Matrix.nonsing_inv_mul_cancel_left _ _ hC]
  have h0 : unitG n F (act g Y) = 0 := Set.indicator_of_notMem hgY _
  simp [h0]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasCompactSupportJacquetRallisOrbitalIntegrandStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasCompactSupport_jacquetRallisOrbitalIntegrand : ∀ (F : Type) [NontriviallyNormedField F] [LocallyCompactSpace F] (n : ℕ) (Y : Gl n F), Delta (inv Y) ≠ 0 → HasCompactSupport (fun g : GL (Fin n) F => unitG n F (act g Y) * omega (act g Y)) := by
  first | exact @GlobalTheory.JR.orbG_integrand_hasCompactSupport | exact GlobalTheory.JR.orbG_integrand_hasCompactSupport | (intros; apply GlobalTheory.JR.orbG_integrand_hasCompactSupport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsClosedEmbeddingDiagOneGeneralLinearEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsClosedEmbeddingDiagOneGeneralLinearEmbedding
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.JR.Step.EmbClosed

theorem embHom_castSucc {r : ℕ} {k : Type} [CommRing k] (g : Matrix (Fin r) (Fin r) k) (i j : Fin r) :
    embHom r k g (Fin.castSucc i) (Fin.castSucc j) = g i j := by
  simp [embHom, Matrix.reindex_apply, finSumFinEquiv_symm_apply_castSucc]

theorem continuous_embHom (r : ℕ) (F : Type) [NontriviallyNormedField F] :
    Continuous (embHom r F) := by
  show Continuous fun g : Matrix (Fin r) (Fin r) F =>
    Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g 0 0 1)
  exact (Continuous.matrix_fromBlocks continuous_id continuous_const continuous_const
    continuous_const).matrix_reindex _ _

theorem isClosedEmbedding_embHom (r : ℕ) (F : Type) [NontriviallyNormedField F] :
    IsClosedEmbedding (embHom r F) :=
  Function.LeftInverse.isClosedEmbedding
    (f := fun x : Matrix (Fin (r + 1)) (Fin (r + 1)) F => x.submatrix Fin.castSucc Fin.castSucc)
    (fun g => by ext i j; exact embHom_castSucc g i j)
    (Continuous.matrix_submatrix continuous_id _ _) (continuous_embHom r F)

theorem isClosedEmbedding_emb (F : Type) [NontriviallyNormedField F] (r : ℕ) :
    IsClosedEmbedding (emb r F) := by
  have hE := isClosedEmbedding_embHom r F
  let Φ : Matrix (Fin r) (Fin r) F × (Matrix (Fin r) (Fin r) F)ᵐᵒᵖ →
      Matrix (Fin (r + 1)) (Fin (r + 1)) F × (Matrix (Fin (r + 1)) (Fin (r + 1)) F)ᵐᵒᵖ :=
    Prod.map (embHom r F) (MulOpposite.op ∘ embHom r F ∘ MulOpposite.unop)
  have hΦ : IsClosedEmbedding Φ := by
    refine hE.prodMap ?_
    exact MulOpposite.opHomeomorph.isClosedEmbedding.comp
      (hE.comp MulOpposite.opHomeomorph.symm.isClosedEmbedding)
  have hcomm : Units.embedProduct _ ∘ emb r F = Φ ∘ Units.embedProduct _ := by
    funext g
    rfl
  rw [← (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin (r + 1)) (Fin (r + 1)) F)).of_comp_iff, hcomm]
  exact hΦ.comp Units.isClosedEmbedding_embedProduct

end GlobalTheory.JR.Step.EmbClosed
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsClosedEmbeddingDiagOneGeneralLinearEmbeddingStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosedEmbedding_diagOneGeneralLinearEmbedding : ∀ (F : Type) [NontriviallyNormedField F] (r : ℕ), Topology.IsClosedEmbedding (GlobalTheory.JR.Step.emb r F) := by
  first | exact @GlobalTheory.JR.Step.EmbClosed.isClosedEmbedding_emb | exact GlobalTheory.JR.Step.EmbClosed.isClosedEmbedding_emb | (intros; apply GlobalTheory.JR.Step.EmbClosed.isClosedEmbedding_emb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisTransferFactorGlBorderedConjugation
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisTransferFactorGlBorderedConjugation
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.OmegaInv

theorem norm_det_le_one {F : Type} [NormedField F] [IsUltrametricDist F] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) (hA : ∀ i j, ‖A i j‖ ≤ 1) : ‖A.det‖ ≤ 1 := by
  rw [Matrix.det_apply']
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  rw [norm_mul, norm_prod]
  have hs : ‖((Equiv.Perm.sign σ : ℤ) : F)‖ ≤ 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  exact mul_le_one₀ hs (Finset.prod_nonneg fun _ _ => norm_nonneg _) (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => hA _ _)

theorem eta_congr {F : Type} [NormedField F] {x y : F} (h : ‖x‖ = ‖y‖) : eta x = eta y := by
  have hiff : (∃ z : F, ‖x‖ = ‖z‖ ^ 2) ↔ (∃ z : F, ‖y‖ = ‖z‖ ^ 2) := by rw [h]
  unfold eta
  split_ifs <;> tauto

theorem omega_act (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] (n : ℕ)
    (k : GL (Fin n) F) (hk : k ∈ glO n F) (Y : Gl n F) : omega (act k Y) = omega Y := by
  unfold omega
  apply eta_congr
  have h1 := (GlobalTheory.JR.transfer_factor_lemma F n).1
  have h2 := (GlobalTheory.JR.transfer_factor_lemma F n).2
  have hl : lastDet (act k Y) = lastDet Y * ((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det := by
    rw [h1, h1, h2, Matrix.det_mul, mul_assoc]
  have ha := norm_det_le_one _ (fun i j => (hk i j).1)
  have hb := norm_det_le_one _ (fun i j => (hk i j).2)
  have hprod : ‖(k : Matrix (Fin n) (Fin n) F).det‖ * ‖((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det‖ = 1 := by
    rw [← norm_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, norm_one]
  have hkinv : ‖((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det‖ = 1 := by
    apply le_antisymm hb
    by_contra hlt
    push_neg at hlt
    have : ‖(k : Matrix (Fin n) (Fin n) F).det‖ * ‖((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det‖ < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) ha) hlt
    linarith
  rw [hl, norm_mul, hkinv, mul_one]

end GlobalTheory.JR.OmegaInv

theorem GlobalTheory.JR.omega_act_glO : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] (n : ℕ) (k : GL (Fin n) F), k ∈ glO n F → ∀ Y : Gl n F, omega (act k Y) = omega Y :=
  fun F _ _ n k hk Y => GlobalTheory.JR.OmegaInv.omega_act F n k hk Y
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisTransferFactorGlBorderedConjugationStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetRallisTransferFactor_glBorderedConjugationAction_integral : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] (n : ℕ) (k : GL (Fin n) F), k ∈ glO n F → ∀ Y : Gl n F, omega (act k Y) = omega Y := by
  first | exact @GlobalTheory.JR.omega_act_glO | exact GlobalTheory.JR.omega_act_glO | (intros; apply GlobalTheory.JR.omega_act_glO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitIndicatorGLBlockLiftBlockMatrixWithLastBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitIndicatorGLBlockLiftBlockMatrixWithLastBasis
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.UnitGLift

variable {k : Type} [CommRing k] {r : ℕ}

theorem full_apply_cc (Y : Gl r k) (a b : Fin r) : full Y (Fin.castSucc a) (Fin.castSucc b) = Y.1 a b := by
  simp [full, Matrix.reindex_apply, Matrix.submatrix_apply]

theorem full_apply_cl (Y : Gl r k) (a : Fin r) : full Y (Fin.castSucc a) (Fin.last r) = Y.2.1 a := by
  simp [full, Matrix.reindex_apply, Matrix.submatrix_apply]

theorem full_apply_lc (Y : Gl r k) (b : Fin r) : full Y (Fin.last r) (Fin.castSucc b) = Y.2.2.1 b := by
  simp [full, Matrix.reindex_apply, Matrix.submatrix_apply]

theorem full_apply_ll (Y : Gl r k) : full Y (Fin.last r) (Fin.last r) = Y.2.2.2 := by
  simp [full, Matrix.reindex_apply, Matrix.submatrix_apply]

end GlobalTheory.JR.UnitGLift

namespace GlobalTheory.JR.UnitGLift

theorem norm_full_le_one_iff {F : Type} [NormedField F] {r : ℕ} (Z : Gl r F) :
    (∀ i j, ‖full Z i j‖ ≤ 1) ↔
      ((∀ i j, ‖Z.1 i j‖ ≤ 1) ∧ (∀ i, ‖Z.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Z.2.2.1 i‖ ≤ 1) ∧ ‖Z.2.2.2‖ ≤ 1) := by
  constructor
  · intro h
    refine ⟨fun i j => ?_, fun i => ?_, fun j => ?_, ?_⟩
    · simpa [full_apply_cc] using h (Fin.castSucc i) (Fin.castSucc j)
    · simpa [full_apply_cl] using h (Fin.castSucc i) (Fin.last r)
    · simpa [full_apply_lc] using h (Fin.last r) (Fin.castSucc j)
    · simpa [full_apply_ll] using h (Fin.last r) (Fin.last r)
  · rintro ⟨h1, h2, h3, h4⟩ i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simpa [full_apply_ll] using h4
      | cast j => simpa [full_apply_lc] using h3 j
    | cast i =>
      induction j using Fin.lastCases with
      | last => simpa [full_apply_cl] using h2 i
      | cast j => simpa [full_apply_cc] using h1 i j

theorem norm_eL_le_one {F : Type} [NormedField F] {r : ℕ} (i : Fin (r + 1)) :
    ‖GlobalTheory.JR.Step.eL r F i‖ ≤ 1 := by
  unfold GlobalTheory.JR.Step.eL
  by_cases h : i = Fin.last r
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem unitG_lift : ∀ (F : Type) [NormedField F] (r : ℕ) (Z : Gl r F) (μ l : F), ‖μ‖ ≤ 1 →
    unitG (r + 1) F (GlobalTheory.JR.Step.lift Z μ l) = (if ‖l‖ ≤ 1 then 1 else 0) * unitG r F Z := by
  intro F _ r Z μ l hμ
  have hb : ∀ i, ‖(μ • GlobalTheory.JR.Step.eL r F) i‖ ≤ 1 := fun i => by
    rw [Pi.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_one₀ hμ (norm_nonneg _) (norm_eL_le_one i)
  have hmem : GlobalTheory.JR.Step.lift Z μ l ∈
      {Y : Gl (r + 1) F | (∀ i j, ‖Y.1 i j‖ ≤ 1) ∧ (∀ i, ‖Y.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Y.2.2.1 i‖ ≤ 1) ∧ ‖Y.2.2.2‖ ≤ 1} ↔
      (Z ∈ {Y : Gl r F | (∀ i j, ‖Y.1 i j‖ ≤ 1) ∧ (∀ i, ‖Y.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Y.2.2.1 i‖ ≤ 1) ∧ ‖Y.2.2.2‖ ≤ 1}
        ∧ ‖l‖ ≤ 1) := by
    simp only [Set.mem_setOf_eq, GlobalTheory.JR.Step.lift]
    rw [norm_full_le_one_iff]
    exact ⟨fun ⟨h1, _, _, h4⟩ => ⟨h1, h4⟩, fun ⟨h1, h4⟩ => ⟨h1, hb, norm_eL_le_one, h4⟩⟩
  unfold unitG
  by_cases hZ : Z ∈ {Y : Gl r F | (∀ i j, ‖Y.1 i j‖ ≤ 1) ∧ (∀ i, ‖Y.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Y.2.2.1 i‖ ≤ 1) ∧ ‖Y.2.2.2‖ ≤ 1}
  · by_cases hl : ‖l‖ ≤ 1
    · rw [Set.indicator_of_mem (hmem.2 ⟨hZ, hl⟩), Set.indicator_of_mem hZ, if_pos hl]
      simp
    · rw [Set.indicator_of_notMem (fun h => hl (hmem.1 h).2), if_neg hl, zero_mul]
  · rw [Set.indicator_of_notMem (fun h => hZ (hmem.1 h).1), Set.indicator_of_notMem hZ, mul_zero]

end GlobalTheory.JR.UnitGLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitIndicatorGLBlockLiftBlockMatrixWithLastBasisStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitIndicatorGLBlock_liftBlockMatrixWithLastBasis : ∀ (F : Type) [NormedField F] (r : ℕ) (Z : Gl r F) (μ l : F), ‖μ‖ ≤ 1 → unitG (r + 1) F (GlobalTheory.JR.Step.lift Z μ l) = (if ‖l‖ ≤ 1 then 1 else 0) * unitG r F Z := by
  first | exact @GlobalTheory.JR.UnitGLift.unitG_lift | exact GlobalTheory.JR.UnitGLift.unitG_lift | (intros; apply GlobalTheory.JR.UnitGLift.unitG_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralGLSetIsOpenAndIsCompact
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralGLSetIsOpenAndIsCompact
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.GLift

theorem glO_isOpen_isCompact : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [ProperSpace F] (n : ℕ), IsOpen (glO n F) ∧ IsCompact (glO n F) := by
  intro F _ _ _ n
  let B : Set (Matrix (Fin n) (Fin n) F) :=
    Set.pi Set.univ (fun _ : Fin n => Set.pi Set.univ (fun _ : Fin n => Metric.closedBall (0 : F) 1))
  have hB : ∀ A : Matrix (Fin n) (Fin n) F, A ∈ B ↔ ∀ i j, ‖A i j‖ ≤ 1 := by
    intro A
    constructor
    · intro h i j
      have := h i (Set.mem_univ _) j (Set.mem_univ _)
      simpa using this
    · intro h i _ j _
      simpa using h i j
  have hBo : IsOpen B :=
    isOpen_set_pi Set.finite_univ fun _ _ =>
      isOpen_set_pi Set.finite_univ fun _ _ => IsUltrametricDist.isOpen_closedBall _ one_ne_zero
  have hBc : IsCompact B :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  let S : Set (Matrix (Fin n) (Fin n) F × (Matrix (Fin n) (Fin n) F)ᵐᵒᵖ) :=
    B ×ˢ (MulOpposite.unop ⁻¹' B)
  have hS : glO n F = Units.embedProduct _ ⁻¹' S := by
    ext g
    simp only [glO, Set.mem_setOf_eq, Set.mem_preimage, S, Set.mem_prod, hB, Units.embedProduct_apply,
      MulOpposite.unop_op]
    constructor
    · intro h; exact ⟨fun i j => (h i j).1, fun i j => (h i j).2⟩
    · intro h i j; exact ⟨h.1 i j, h.2 i j⟩
  have hSo : IsOpen S := hBo.prod (hBo.preimage MulOpposite.continuous_unop)
  have hSc : IsCompact S := by
    refine hBc.prod ?_
    have : MulOpposite.unop ⁻¹' B = MulOpposite.op '' B := by
      ext x
      constructor
      · intro h; exact ⟨_, h, MulOpposite.op_unop x⟩
      · rintro ⟨y, hy, rfl⟩; simpa using hy
    rw [this]; exact hBc.image MulOpposite.continuous_op
  rw [hS]
  exact ⟨hSo.preimage Units.continuous_embedProduct,
    Units.isClosedEmbedding_embedProduct.isCompact_preimage hSc⟩

end GlobalTheory.JR.GLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralGLSetIsOpenAndIsCompactStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralGLSet_isOpen_and_isCompact : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [ProperSpace F] (n : ℕ), IsOpen (glO n F) ∧ IsCompact (glO n F) := by
  first | exact @GlobalTheory.JR.GLift.glO_isOpen_isCompact | exact GlobalTheory.JR.GLift.glO_isOpen_isCompact | (intros; apply GlobalTheory.JR.GLift.glO_isOpen_isCompact <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BorderedConjugationDiagOneLiftBlockMatrix
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BorderedConjugationDiagOneLiftBlockMatrix
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.Step.ActEmbLift

theorem embHom_mul_full_mul (k : Type) [CommRing k] (r : ℕ) (g h : Matrix (Fin r) (Fin r) k) (Z : Gl r k) :
    embHom r k g * full Z * embHom r k h = full (g * Z.1 * h, g *ᵥ Z.2.1, Z.2.2.1 ᵥ* h, Z.2.2.2) := by
  simp only [embHom, MonoidHom.coe_mk, OneHom.coe_mk, full, Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  congr 2
  · simp
  · ext i j; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  · ext i j; simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
  · ext i j; simp [Matrix.mul_apply]

theorem embHom_mulVec_eL (k : Type) [CommRing k] (r : ℕ) (g : Matrix (Fin r) (Fin r) k) :
    embHom r k g *ᵥ eL r k = eL r k := by
  ext i
  simp only [embHom, MonoidHom.coe_mk, OneHom.coe_mk, eL, Matrix.reindex_apply]
  rw [Matrix.mulVec_single_one]
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [Matrix.transpose_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_last]
  · simp [Matrix.transpose_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_last, finSumFinEquiv_symm_apply_castSucc]

theorem eL_vecMul_embHom (k : Type) [CommRing k] (r : ℕ) (g : Matrix (Fin r) (Fin r) k) :
    eL r k ᵥ* embHom r k g = eL r k := by
  ext i
  simp only [embHom, MonoidHom.coe_mk, OneHom.coe_mk, eL, Matrix.reindex_apply]
  rw [Matrix.single_one_vecMul]
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [Matrix.submatrix_apply, finSumFinEquiv_symm_last]
  · simp [Matrix.submatrix_apply, finSumFinEquiv_symm_last, finSumFinEquiv_symm_apply_castSucc]

theorem act_emb_lift (k : Type) [CommRing k] (r : ℕ) (g : GL (Fin r) k) (Z : Gl r k) (μ l : k) :
    act (GlobalTheory.JR.Step.emb r k g) (GlobalTheory.JR.Step.lift Z μ l) = GlobalTheory.JR.Step.lift (act g Z) μ l := by
  have hinv : ((emb r k g)⁻¹ : GL (Fin (r + 1)) k) = emb r k g⁻¹ := (map_inv _ _).symm
  simp only [act, lift, hinv, emb, Units.coe_map, MonoidHom.coe_coe]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl))
  · exact embHom_mul_full_mul k r _ _ Z
  · simp only [Matrix.mulVec_smul, embHom_mulVec_eL]
  · exact eL_vecMul_embHom k r _

end GlobalTheory.JR.Step.ActEmbLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BorderedConjugationDiagOneLiftBlockMatrixStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.borderedConjugation_diagOne_liftBlockMatrix : ∀ (k : Type) [CommRing k] (r : ℕ) (g : GL (Fin r) k) (Z : Gl r k) (μ l : k), act (GlobalTheory.JR.Step.emb r k g) (GlobalTheory.JR.Step.lift Z μ l) = GlobalTheory.JR.Step.lift (act g Z) μ l := by
  first | exact @GlobalTheory.JR.Step.ActEmbLift.act_emb_lift | exact GlobalTheory.JR.Step.ActEmbLift.act_emb_lift | (intros; apply GlobalTheory.JR.Step.ActEmbLift.act_emb_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralGLMulDiagOneOfUnitIndicatorLiftNeZ
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLeMaxUltra
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.LatL

theorem norm_sub_le_max_ultra' {K : Type} [NormedField K] [IsUltrametricDist K] (x y : K) :
    ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg, ← norm_neg y]
  exact IsUltrametricDist.norm_add_le_max _ _

theorem exists_glO_pair {F : Type} [NormedField F] [IsUltrametricDist F] (r : ℕ)
    (v w : Fin (r + 1) → F) (hv : ∀ i, ‖v i‖ ≤ 1) (hw : ∀ i, ‖w i‖ ≤ 1) (hwv : w ⬝ᵥ v = 1) :
    ∃ k ∈ glO (r + 1) F, (k : Matrix _ _ F) *ᵥ Pi.single (Fin.last r) 1 = v ∧
      w ᵥ* (k : Matrix _ _ F) = Pi.single (Fin.last r) 1 := by
  classical
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max (fun i => ‖w i‖)
  have hw0 : w i₀ ≠ 0 := by
    intro h
    have : w = 0 := funext fun i => norm_le_zero_iff.mp (by simpa [h] using hi₀ i)
    simp [this] at hwv
  have hratio : ∀ i, ‖w i / w i₀‖ ≤ 1 := fun i => by
    rw [norm_div]; exact div_le_one_of_le₀ (hi₀ i) (norm_nonneg _)
  let s : Fin r → Fin (r + 1) := i₀.succAbove
  have hs : ∀ c, s c ≠ i₀ := fun c => Fin.succAbove_ne i₀ c
  let u : Fin r → Fin (r + 1) → F := fun c =>
    Pi.single (s c) 1 - (w (s c) / w i₀) • Pi.single i₀ 1
  let ρ : Fin r → Fin (r + 1) → F := fun c => Pi.single (s c) 1 - v (s c) • w
  let col : Fin (r + 1) → Fin (r + 1) → F := Fin.lastCases v u
  let row : Fin (r + 1) → Fin (r + 1) → F := Fin.lastCases w ρ
  let K : Matrix (Fin (r + 1)) (Fin (r + 1)) F := Matrix.of fun a b => col b a
  let L : Matrix (Fin (r + 1)) (Fin (r + 1)) F := Matrix.of fun a b => row a b
  have hwu : ∀ c, w ⬝ᵥ u c = 0 := by
    intro c
    simp only [u, dotProduct_sub, dotProduct_smul, dotProduct_single, smul_eq_mul, mul_one]
    field_simp; ring
  have hdot : ∀ a b, row a ⬝ᵥ col b = (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) F) a b := by
    intro a b
    induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last => simp [row, col, hwv]
      | cast c => simp [row, col, hwu, Matrix.one_apply, (Fin.castSucc_lt_last c).ne']
    | cast c =>
      induction b using Fin.lastCases with
      | last =>
        simp [row, col, ρ, sub_dotProduct, smul_dotProduct, single_dotProduct, hwv,
          Matrix.one_apply, (Fin.castSucc_lt_last c).ne]
      | cast c' =>
        simp only [row, col, Fin.lastCases_castSucc, ρ, sub_dotProduct, smul_dotProduct,
          single_dotProduct, hwu, smul_eq_mul, mul_zero, sub_zero, one_mul, u, Pi.sub_apply,
          Pi.smul_apply, Pi.single_apply, hs c, if_false, mul_zero, sub_zero, Matrix.one_apply,
          Fin.castSucc_inj]
        by_cases h : c = c'
        · subst h; simp
        · have : s c ≠ s c' := fun e => h (Fin.succAbove_right_injective e)
          simp [this, h]
  have hLK : L * K = 1 := by
    ext a b
    rw [← hdot a b]
    simp [L, K, Matrix.mul_apply, dotProduct]
  have hKL : K * L = 1 := mul_eq_one_comm.mp hLK
  let k : GL (Fin (r + 1)) F := ⟨K, L, hKL, hLK⟩
  have hsingle : ∀ i j : Fin (r + 1), ‖(Pi.single i (1 : F) : Fin (r + 1) → F) j‖ ≤ 1 := by
    intro i j; by_cases h : j = i
    · subst h; simp
    · simp [Pi.single_apply, h]
  have hcol : ∀ b a, ‖col b a‖ ≤ 1 := by
    intro b a
    induction b using Fin.lastCases with
    | last => simpa [col] using hv a
    | cast c =>
      simp only [col, Fin.lastCases_castSucc, u, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      refine (norm_sub_le_max_ultra' _ _).trans (max_le (hsingle _ _) ?_)
      rw [norm_mul]
      exact mul_le_one₀ (hratio _) (norm_nonneg _) (hsingle _ _)
  have hrow : ∀ a b, ‖row a b‖ ≤ 1 := by
    intro a b
    induction a using Fin.lastCases with
    | last => simpa [row] using hw b
    | cast c =>
      simp only [row, Fin.lastCases_castSucc, ρ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      refine (norm_sub_le_max_ultra' _ _).trans (max_le (hsingle _ _) ?_)
      rw [norm_mul]
      exact mul_le_one₀ (hv _) (norm_nonneg _) (hw _)
  refine ⟨k, fun i j => ⟨by simpa [k, K] using hcol j i, by simpa [k, L] using hrow i j⟩, ?_, ?_⟩
  · rw [Matrix.mulVec_single_one]
    funext a
    change col (Fin.last r) a = v a
    simp [col]
  · ext b
    rw [show (w ᵥ* (k : Matrix _ _ F)) b = row (Fin.last r) ⬝ᵥ col b by
      simp [k, K, row, Matrix.vecMul, dotProduct]]
    rw [hdot, Matrix.one_apply, Pi.single_apply]
    simp only [eq_comm]

theorem glO_transitive_pairs : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (v w : Fin (r + 1) → F), (∀ i, ‖v i‖ ≤ 1) →
    (∀ i, ‖w i‖ ≤ 1) → w ⬝ᵥ v = 1 → ∃ k ∈ glO (r + 1) F,
      (k : Matrix _ _ F) *ᵥ Pi.single (Fin.last r) 1 = v ∧ w ᵥ* (k : Matrix _ _ F) = Pi.single (Fin.last r) 1 := by
  intro F E _ _ _ _ hU r v w hv hw hwv
  haveI : IsUltrametricDist F := hU.ultraF
  exact exists_glO_pair r v w hv hw hwv

end GlobalTheory.LatL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralGLMulDiagOneOfUnitIndicatorLiftNeZ
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.GLift

theorem exists_emb_of_last {F : Type} [Field F] (r : ℕ) (m : GL (Fin (r + 1)) F)
    (hc : (m : Matrix _ _ F) *ᵥ GlobalTheory.JR.Step.eL r F = GlobalTheory.JR.Step.eL r F)
    (hr : GlobalTheory.JR.Step.eL r F ᵥ* (m : Matrix _ _ F) = GlobalTheory.JR.Step.eL r F) :
    ∃ s : GL (Fin r) F, m = GlobalTheory.JR.Step.emb r F s := by
  classical
  set t : Matrix (Fin r) (Fin r) F := (m : Matrix _ _ F).submatrix Fin.castSucc Fin.castSucc with ht
  have hcol : ∀ i, (m : Matrix _ _ F) i (Fin.last r) = (Pi.single (Fin.last r) (1 : F) : Fin (r + 1) → F) i := by
    intro i
    have := congrFun hc i
    simpa [GlobalTheory.JR.Step.eL, Matrix.mulVec_single_one] using this
  have hrow : ∀ j, (m : Matrix _ _ F) (Fin.last r) j = (Pi.single (Fin.last r) (1 : F) : Fin (r + 1) → F) j := by
    intro j
    have := congrFun hr j
    simpa [GlobalTheory.JR.Step.eL, Matrix.single_one_vecMul] using this
  have hm : (m : Matrix _ _ F) = GlobalTheory.JR.Step.embHom r F t := by
    ext i j
    induction i using Fin.lastCases with
    | last =>
      rw [hrow j]
      induction j using Fin.lastCases with
      | last => simp [GlobalTheory.JR.Step.embHom]
      | cast j => simp [GlobalTheory.JR.Step.embHom, Fin.castSucc_ne_last]
    | cast i =>
      induction j using Fin.lastCases with
      | last => rw [hcol]; simp [GlobalTheory.JR.Step.embHom, Fin.castSucc_ne_last]
      | cast j => simp [GlobalTheory.JR.Step.embHom, ht]
  have hdet : (m : Matrix (Fin (r + 1)) (Fin (r + 1)) F).det = t.det := by
    rw [hm]
    simp [GlobalTheory.JR.Step.embHom, Matrix.det_fromBlocks_zero₂₁]
  have hu : IsUnit t.det := by
    rw [← hdet]
    exact (Matrix.isUnit_iff_isUnit_det (m : Matrix (Fin (r + 1)) (Fin (r + 1)) F)).mp (Units.isUnit m)
  refine ⟨Matrix.nonsingInvUnit t hu, ?_⟩
  ext : 1
  rw [hm]
  rfl

end GlobalTheory.JR.GLift

namespace GlobalTheory.JR.GLift

theorem support_lift : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (Z : Gl r F) (μ l : F), ‖μ‖ = 1 →
    ∀ g : GL (Fin (r + 1)) F, unitG (r + 1) F (act g (GlobalTheory.JR.Step.lift Z μ l)) ≠ 0 →
      ∃ k ∈ glO (r + 1) F, ∃ s : GL (Fin r) F, g = k * GlobalTheory.JR.Step.emb r F s := by
  intro F E _ _ _ _ _ r Z μ l hμ g hg
  classical
  obtain ⟨-, hb, hc, -⟩ := Set.mem_of_indicator_ne_zero hg
  simp only [act, GlobalTheory.JR.Step.lift] at hb hc
  set e : Fin (r + 1) → F := GlobalTheory.JR.Step.eL r F with he
  have hv : ∀ i, ‖((g : Matrix (Fin (r + 1)) (Fin (r + 1)) F) *ᵥ e) i‖ ≤ 1 := by
    intro i
    have := hb i
    rwa [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, norm_mul, hμ, one_mul] at this
  have hw : ∀ i, ‖(e ᵥ* ((g⁻¹ : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F)) i‖ ≤ 1 := hc
  have hgg : ((g⁻¹ : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F) * (g : Matrix (Fin (r + 1)) (Fin (r + 1)) F) = 1 :=
    Units.inv_mul g
  have hee : e ⬝ᵥ e = 1 := by simp [he, GlobalTheory.JR.Step.eL]
  have hwv : (e ᵥ* ((g⁻¹ : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F)) ⬝ᵥ ((g : Matrix (Fin (r + 1)) (Fin (r + 1)) F) *ᵥ e) = 1 := by
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec, hee]
  obtain ⟨k, hk, hkv, hkw⟩ := GlobalTheory.LatL.glO_transitive_pairs F E r _ _ hv hw hwv
  have hkv' : (k : Matrix (Fin (r + 1)) (Fin (r + 1)) F) *ᵥ e = (g : Matrix (Fin (r + 1)) (Fin (r + 1)) F) *ᵥ e := hkv
  have hkw' : (e ᵥ* ((g⁻¹ : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F)) ᵥ* (k : Matrix (Fin (r + 1)) (Fin (r + 1)) F) = e := hkw
  have hkk : ((k⁻¹ : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F) * (k : Matrix (Fin (r + 1)) (Fin (r + 1)) F) = 1 :=
    Units.inv_mul k
  have hkk' : (k : Matrix (Fin (r + 1)) (Fin (r + 1)) F) * ((k⁻¹ : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F) = 1 :=
    Units.mul_inv k
  have hek : e ᵥ* ((k⁻¹ : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F) = e ᵥ* ((g⁻¹ : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F) := by
    conv_lhs => rw [← hkw']
    rw [Matrix.vecMul_vecMul, hkk', Matrix.vecMul_one]
  obtain ⟨s, hs⟩ := exists_emb_of_last r (k⁻¹ * g) (by
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← hkv', Matrix.mulVec_mulVec, hkk, Matrix.one_mulVec])
    (by rw [Units.val_mul, ← Matrix.vecMul_vecMul, hek, Matrix.vecMul_vecMul, hgg, Matrix.vecMul_one])
  exact ⟨k, hk, s, by rw [← hs, mul_inv_cancel_left]⟩

end GlobalTheory.JR.GLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralGLMulDiagOneOfUnitIndicatorLiftNeZStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralGL_mul_diagOne_of_unitIndicator_lift_ne_zero : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (Z : Gl r F) (μ l : F), ‖μ‖ = 1 → ∀ g : GL (Fin (r + 1)) F, unitG (r + 1) F (act g (GlobalTheory.JR.Step.lift Z μ l)) ≠ 0 → ∃ k ∈ glO (r + 1) F, ∃ s : GL (Fin r) F, g = k * GlobalTheory.JR.Step.emb r F s := by
  first | exact @GlobalTheory.JR.GLift.support_lift | exact GlobalTheory.JR.GLift.support_lift | (intros; apply GlobalTheory.JR.GLift.support_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PreimageDiagOneGeneralLinearEmbeddingIntegralGLS
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PreimageDiagOneGeneralLinearEmbeddingIntegralGLS
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.JR.GLift

theorem embHom_apply_cc {F : Type} [CommRing F] {r : ℕ} (a : Matrix (Fin r) (Fin r) F) (i j : Fin r) :
    GlobalTheory.JR.Step.embHom r F a (Fin.castSucc i) (Fin.castSucc j) = a i j := by
  simp [GlobalTheory.JR.Step.embHom, finSumFinEquiv_symm_apply_castSucc]

theorem embHom_apply_cl {F : Type} [CommRing F] {r : ℕ} (a : Matrix (Fin r) (Fin r) F) (i : Fin r) :
    GlobalTheory.JR.Step.embHom r F a (Fin.castSucc i) (Fin.last r) = 0 := by
  simp [GlobalTheory.JR.Step.embHom, finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last]

theorem embHom_apply_lc {F : Type} [CommRing F] {r : ℕ} (a : Matrix (Fin r) (Fin r) F) (j : Fin r) :
    GlobalTheory.JR.Step.embHom r F a (Fin.last r) (Fin.castSucc j) = 0 := by
  simp [GlobalTheory.JR.Step.embHom, finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last]

theorem embHom_apply_ll {F : Type} [CommRing F] {r : ℕ} (a : Matrix (Fin r) (Fin r) F) :
    GlobalTheory.JR.Step.embHom r F a (Fin.last r) (Fin.last r) = 1 := by
  simp [GlobalTheory.JR.Step.embHom, finSumFinEquiv_symm_last]

theorem coe_emb {F : Type} [CommRing F] {r : ℕ} (g : GL (Fin r) F) :
    ((GlobalTheory.JR.Step.emb r F g : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F) =
      GlobalTheory.JR.Step.embHom r F (g : Matrix (Fin r) (Fin r) F) := rfl

theorem coe_emb_inv {F : Type} [CommRing F] {r : ℕ} (g : GL (Fin r) F) :
    (((GlobalTheory.JR.Step.emb r F g)⁻¹ : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F) =
      GlobalTheory.JR.Step.embHom r F ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) := by
  rw [← map_inv]; rfl

theorem emb_preimage_glO : ∀ (F : Type) [NormedField F] (r : ℕ),
    ⇑(GlobalTheory.JR.Step.emb r F) ⁻¹' glO (r + 1) F = glO r F := by
  intro F _ r
  ext g
  simp only [Set.mem_preimage, glO, Set.mem_setOf_eq, coe_emb, coe_emb_inv]
  constructor
  · intro h i j
    have := h (Fin.castSucc i) (Fin.castSucc j)
    rwa [embHom_apply_cc, embHom_apply_cc] at this
  · intro h i j
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [embHom_apply_ll]
    · simp [embHom_apply_lc]
    · simp [embHom_apply_cl]
    · rw [embHom_apply_cc, embHom_apply_cc]; exact h i j

end GlobalTheory.JR.GLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PreimageDiagOneGeneralLinearEmbeddingIntegralGLSStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.preimage_diagOneGeneralLinearEmbedding_integralGLSet : ∀ (F : Type) [NormedField F] (r : ℕ), ⇑(GlobalTheory.JR.Step.emb r F) ⁻¹' glO (r + 1) F = glO r F := by
  first | exact @GlobalTheory.JR.GLift.emb_preimage_glO | exact GlobalTheory.JR.GLift.emb_preimage_glO | (intros; apply GlobalTheory.JR.GLift.emb_preimage_glO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitIndicatorGLBlockGlBorderedConjugationActionI
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitIndicatorGLBlockGlBorderedConjugationActionI
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.GLift

theorem norm_mulVec_apply_le_one {F : Type} [NormedField F] [IsUltrametricDist F] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) (v : Fin n → F) (hA : ∀ i j, ‖A i j‖ ≤ 1) (hv : ∀ i, ‖v i‖ ≤ 1)
    (i : Fin n) : ‖(A *ᵥ v) i‖ ≤ 1 := by
  rw [Matrix.mulVec, dotProduct]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hA i k) (norm_nonneg _) (hv k)

theorem norm_vecMul_apply_le_one {F : Type} [NormedField F] [IsUltrametricDist F] {n : ℕ}
    (v : Fin n → F) (A : Matrix (Fin n) (Fin n) F) (hv : ∀ i, ‖v i‖ ≤ 1) (hA : ∀ i j, ‖A i j‖ ≤ 1)
    (j : Fin n) : ‖(v ᵥ* A) j‖ ≤ 1 := by
  rw [Matrix.vecMul, dotProduct]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hv k) (norm_nonneg _) (hA k j)

def IsIntegral {F : Type} [NormedField F] {n : ℕ} (Y : Gl n F) : Prop :=
  (∀ i j, ‖Y.1 i j‖ ≤ 1) ∧ (∀ i, ‖Y.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Y.2.2.1 i‖ ≤ 1) ∧ ‖Y.2.2.2‖ ≤ 1

theorem isIntegral_act {F : Type} [NormedField F] [IsUltrametricDist F] {n : ℕ} {k : GL (Fin n) F}
    (hk : k ∈ glO n F) {Y : Gl n F} (hY : IsIntegral Y) : IsIntegral (act k Y) := by
  obtain ⟨h1, h2, h3, h4⟩ := hY
  refine ⟨fun i j => ?_, fun i => ?_, fun i => ?_, h4⟩
  · exact norm_mul_apply_le_one _ _
      (fun i j => norm_mul_apply_le_one _ _ (fun i j => (hk i j).1) h1 i j) (fun i j => (hk i j).2) i j
  · exact norm_mulVec_apply_le_one _ _ (fun i j => (hk i j).1) h2 i
  · exact norm_vecMul_apply_le_one _ _ h3 (fun i j => (hk i j).2) i

theorem act_inv_act {F : Type} [Field F] {n : ℕ} (k : GL (Fin n) F) (Y : Gl n F) :
    act k⁻¹ (act k Y) = Y := by
  obtain ⟨A, b, c, l⟩ := Y
  simp only [act, inv_inv, Matrix.mulVec_mulVec, Matrix.vecMul_vecMul]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl))
  · show ((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * ((k : Matrix (Fin n) (Fin n) F) * A *
        ((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) * (k : Matrix (Fin n) (Fin n) F) = A
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc,
      Units.inv_mul, Matrix.mul_one]
  · show (((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (k : Matrix (Fin n) (Fin n) F)) *ᵥ b = b
    rw [Units.inv_mul, Matrix.one_mulVec]
  · show c ᵥ* (((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (k : Matrix (Fin n) (Fin n) F)) = c
    rw [Units.inv_mul, Matrix.vecMul_one]

theorem unitG_act : ∀ (F : Type) [NormedField F] [IsUltrametricDist F] (n : ℕ) (k : GL (Fin n) F),
    k ∈ glO n F → ∀ Y : Gl n F, unitG n F (act k Y) = unitG n F Y := by
  intro F _ _ n k hk Y
  have hk' : k⁻¹ ∈ glO n F := (glOSub n F).inv_mem hk
  have key : IsIntegral (act k Y) ↔ IsIntegral Y :=
    ⟨fun h => act_inv_act k Y ▸ isIntegral_act hk' h, isIntegral_act hk⟩
  have e : ∀ Z : Gl n F, unitG n F Z = Set.indicator {Z | IsIntegral Z} 1 Z := fun _ => rfl
  rw [e, e]
  by_cases h : IsIntegral Y
  · rw [Set.indicator_of_mem (show act k Y ∈ {Z | IsIntegral Z} from key.2 h),
      Set.indicator_of_mem (show Y ∈ {Z | IsIntegral Z} from h)]
    rfl
  · rw [Set.indicator_of_notMem (show act k Y ∉ {Z | IsIntegral Z} from fun h' => h (key.1 h')),
      Set.indicator_of_notMem (show Y ∉ {Z | IsIntegral Z} from h)]

end GlobalTheory.JR.GLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitIndicatorGLBlockGlBorderedConjugationActionIStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitIndicatorGLBlock_glBorderedConjugationAction_integral : ∀ (F : Type) [NormedField F] [IsUltrametricDist F] (n : ℕ) (k : GL (Fin n) F), k ∈ glO n F → ∀ Y : Gl n F, unitG n F (act k Y) = unitG n F Y := by
  first | exact @GlobalTheory.JR.GLift.unitG_act | exact GlobalTheory.JR.GLift.unitG_act | (intros; apply GlobalTheory.JR.GLift.unitG_act <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlOrbitalIntegralUnitLiftLastBasisReduce
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.GLift

theorem act_mul' {k : Type} [CommRing k] {n : ℕ} (g h : GL (Fin n) k) (Y : Gl n k) :
    act (g * h) Y = act g (act h Y) := by
  simp only [act, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, Matrix.mulVec_mulVec, Matrix.vecMul_vecMul]

theorem omega_lift {F : Type} [NontriviallyNormedField F] (r : ℕ) (Z : Gl r F) (μ l : F) :
    omega (GlobalTheory.JR.Step.lift Z μ l) = omega Z := by
  have h := (GlobalTheory.JR.transfer_factor_lemma F (r + 1)).1 (GlobalTheory.JR.Step.lift Z μ l)
  have hc : (Cm (GlobalTheory.JR.Step.lift Z μ l)).det = lastDet Z := rfl
  unfold omega eta
  rw [h, hc, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]

theorem orbG_lift : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (M : Meas (r + 1) F E) (M' : Meas r F E) (Z : Gl r F) (μ l : F), ‖μ‖ = 1 →
    Delta (inv (GlobalTheory.JR.Step.lift Z μ l)) ≠ 0 →
    orbG M (unitG (r + 1) F) (GlobalTheory.JR.Step.lift Z μ l) = (if ‖l‖ ≤ 1 then 1 else 0) * orbG M' (unitG r F) Z := by
  intro F E _ _ _ _ hU r M M' Z μ l hμ hΔ
  haveI := hU.ultraF
  haveI := hU.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  obtain ⟨lc1, sc1⟩ := gl_lc_sc F (r + 1)
  letI := M.mG
  haveI := M.bG
  letI := M'.mG
  haveI := M'.bG
  haveI := M.haarG
  haveI := M'.haarG
  haveI := gl_unimodular F E (r + 1) M
  haveI := gl_unimodular F E r M'
  obtain ⟨hO, hC⟩ := GlobalTheory.T.integralGLSet_isOpen_and_isCompact F (r + 1)
  have hemb := GlobalTheory.T.isClosedEmbedding_diagOneGeneralLinearEmbedding F r
  have key := GlobalTheory.CosetIntegral.integral_eq_of_coset_support (GL (Fin (r + 1)) F) (GL (Fin r) F)
    (GlobalTheory.JR.Step.emb r F) hemb M.μG M'.μG (glOSub (r + 1) F) hO hC M.volG
    (by rw [coe_glOSub, GlobalTheory.T.preimage_diagOneGeneralLinearEmbedding_integralGLSet F r]; exact M'.volG)
    (fun g => unitG (r + 1) F (act g (GlobalTheory.JR.Step.lift Z μ l)) * omega (act g (GlobalTheory.JR.Step.lift Z μ l)))
    (fun k hk g => by
      simp only [act_mul', GlobalTheory.T.unitIndicatorGLBlock_glBorderedConjugationAction_integral F (r + 1) k hk, GlobalTheory.T.jacquetRallisTransferFactor_glBorderedConjugationAction_integral F (r + 1) k hk])
    (fun g hg => GlobalTheory.T.exists_integralGL_mul_diagOne_of_unitIndicator_lift_ne_zero F E r Z μ l hμ g (left_ne_zero_of_mul hg))
    ((GlobalTheory.T.hasCompactSupport_jacquetRallisOrbitalIntegrand F (r + 1) _ hΔ).comp_isClosedEmbedding hemb)
  unfold orbG
  rw [key]
  simp only [GlobalTheory.T.borderedConjugation_diagOne_liftBlockMatrix, GlobalTheory.T.unitIndicatorGLBlock_liftBlockMatrixWithLastBasis F r _ μ l hμ.le, omega_lift, mul_assoc]
  exact integral_const_mul _ _

end GlobalTheory.JR.GLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlOrbitalIntegralUnitLiftLastBasisReduceStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glOrbitalIntegral_unit_liftLastBasis_reduce : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas (r + 1) F E) (M' : Meas r F E) (Z : Gl r F) (μ l : F), ‖μ‖ = 1 → Delta (inv (GlobalTheory.JR.Step.lift Z μ l)) ≠ 0 → orbG M (unitG (r + 1) F) (GlobalTheory.JR.Step.lift Z μ l) = (if ‖l‖ ≤ 1 then 1 else 0) * orbG M' (unitG r F) Z := by
  first | exact @GlobalTheory.JR.GLift.orbG_lift | exact GlobalTheory.JR.GLift.orbG_lift | (intros; apply GlobalTheory.JR.GLift.orbG_lift <;> assumption)
end
