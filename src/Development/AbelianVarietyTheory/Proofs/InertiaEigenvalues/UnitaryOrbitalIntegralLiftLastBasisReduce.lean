module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralSumIndicatorTranslate
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryGroupPositiveCharacterTrivialAndUnimodula
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryActLiftHermitianBlockMemIntegralUnitaryMu

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCompactUnitariesIntegralOrbitOfHankelDetNe
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCompactUnitariesIntegralOrbitOfHankelDetNe
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.SuppBdd

theorem isClosed_unitary_set {n : ℕ} {E : Type} [Field E] [TopologicalSpace E] [IsTopologicalRing E] [T2Space E]
    [StarRing E] [ContinuousStar E] :
    IsClosed ((Matrix.unitaryGroup (Fin n) E : Set (Matrix (Fin n) (Fin n) E))) := by
  have : ((Matrix.unitaryGroup (Fin n) E : Set (Matrix (Fin n) (Fin n) E))) =
      {U | star U * U = 1} ∩ {U | U * star U = 1} := by
    ext U; simp [Matrix.unitaryGroup, Unitary.mem_iff]
  rw [this]
  exact (isClosed_eq (continuous_star.mul continuous_id) continuous_const).inter
    (isClosed_eq (continuous_id.mul continuous_star) continuous_const)

theorem pow_conj {n : ℕ} {E : Type} [CommRing E] [StarRing E] (g : Matrix.unitaryGroup (Fin n) E)
    (A : Matrix (Fin n) (Fin n) E) (j : ℕ) : (g.1 * A * star g.1) ^ j = g.1 * A ^ j * star g.1 := by
  have hg : star g.1 * g.1 = 1 := Unitary.star_mul_self_of_mem g.2
  have hg' : g.1 * star g.1 = 1 := Unitary.mul_star_self_of_mem g.2
  induction j with
  | zero => simp [hg']
  | succ j ih =>
    rw [pow_succ, ih, pow_succ]
    calc g.1 * A ^ j * star g.1 * (g.1 * A * star g.1) = g.1 * A ^ j * (star g.1 * g.1) * A * star g.1 := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hg, Matrix.mul_one]; simp only [Matrix.mul_assoc]

theorem Bm_actU {n : ℕ} {F E : Type} [CommRing F] [CommRing E] [StarRing E] [Algebra F E]
    (g : Matrix.unitaryGroup (Fin n) E) (Y : Hn n F E) :
    Bm (actU g Y).toGl = g.1 * Bm Y.toGl := by
  have hg : star g.1 * g.1 = 1 := Unitary.star_mul_self_of_mem g.2
  ext i j
  have h1 : ((g.1 * Y.1.1 * star g.1) ^ (j : ℕ)) *ᵥ (g.1 *ᵥ Y.2.1) = g.1 *ᵥ ((Y.1.1 ^ (j : ℕ)) *ᵥ Y.2.1) := by
    rw [pow_conj, mulVec_mulVec, mulVec_mulVec]
    congr 1
    rw [Matrix.mul_assoc, hg, Matrix.mul_one]
  have h2 : Bm (actU g Y).toGl i j = (g.1 *ᵥ ((Y.1.1 ^ (j : ℕ)) *ᵥ Y.2.1)) i := by
    rw [← h1]; rfl
  rw [h2, Matrix.mul_apply]
  simp only [mulVec, dotProduct, Bm, Hn.toGl, of_apply]

theorem exists_compact_of_integral : ∀ {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] {n : ℕ} (Y : Hn n F E), Delta (inv Y.toGl) ≠ 0 →
    ∃ K : Set (Matrix.unitaryGroup (Fin n) E), IsCompact K ∧ ∀ g, unitU n F E (actU g Y) ≠ 0 → g ∈ K := by
  intro F E _ _ _ _ _ n Y hD
  haveI : LocallyCompactSpace E := Unram.lcE (F := F)
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : NormedStarGroup E := ⟨fun x => (Unram.norm_star (F := F) x).le⟩
  set B := Bm Y.toGl with hBdef
  have hB : IsUnit B.det := by
    have h := GlobalTheory.JR.NormalFormL.hankel_eq Y.toGl
    have : (Cm Y.toGl * B).det ≠ 0 := by rw [h]; exact hD
    rw [det_mul] at this
    exact isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul this)
  let Φ : Matrix (Fin n) (Fin n) E × (Fin n → E) → Matrix (Fin n) (Fin n) E :=
    fun p => (Matrix.of fun i (j : Fin n) => ((p.1 ^ (j : ℕ)) *ᵥ p.2) i) * B⁻¹
  let S : Set (Matrix (Fin n) (Fin n) E × (Fin n → E)) :=
    {A | ∀ i j, ‖A i j‖ ≤ 1} ×ˢ {v | ∀ i, ‖v i‖ ≤ 1}
  have hS : IsCompact S := by
    apply IsCompact.prod
    · have : {A : Matrix (Fin n) (Fin n) E | ∀ i j, ‖A i j‖ ≤ 1} =
          Set.pi Set.univ (fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : E) 1) := by
        ext A; simp only [Set.mem_setOf_eq]
        exact ⟨fun h i _ j _ => by simpa using h i j, fun h i j => by simpa using h i trivial j trivial⟩
      rw [this]
      exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
    · have : {v : Fin n → E | ∀ i, ‖v i‖ ≤ 1} = Set.pi Set.univ (fun _ => Metric.closedBall (0 : E) 1) := by
        ext v; simp
      rw [this]
      exact isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hΦ : Continuous Φ := by
    refine Continuous.matrix_mul ?_ continuous_const
    refine continuous_matrix fun i j => ?_
    exact (continuous_apply i).comp ((continuous_fst.pow (j : ℕ)).matrix_mulVec continuous_snd)
  refine ⟨Subtype.val ⁻¹' (Φ '' S), ?_, ?_⟩
  · exact (isClosed_unitary_set (n := n) (E := E)).isClosedEmbedding_subtypeVal.isCompact_preimage (hS.image hΦ)
  · intro g hg
    have hm := Set.mem_of_indicator_ne_zero hg
    refine ⟨((actU g Y).1.1, (actU g Y).2.1), ⟨hm.1, hm.2.1⟩, ?_⟩
    show Bm (actU g Y).toGl * B⁻¹ = g.1
    rw [Bm_actU, ← hBdef, Matrix.mul_nonsing_inv_cancel_right _ _ hB]

end GlobalTheory.JR.SuppBdd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCompactUnitariesIntegralOrbitOfHankelDetNeStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compact_unitaries_integral_orbit_of_hankelDet_ne_zero : ∀ {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] {n : ℕ} (Y : Hn n F E), Delta (inv Y.toGl) ≠ 0 → ∃ K : Set (Matrix.unitaryGroup (Fin n) E), IsCompact K ∧ ∀ g, unitU n F E (actU g Y) ≠ 0 → g ∈ K := by
  first | exact @GlobalTheory.JR.SuppBdd.exists_compact_of_integral | exact GlobalTheory.JR.SuppBdd.exists_compact_of_integral | (intros; apply GlobalTheory.JR.SuppBdd.exists_compact_of_integral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryActHermitianBlockDiagOneLiftLastBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryActHermitianBlockDiagOneLiftLastBasis
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Step

theorem actU_uEmb_liftH {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] {r : ℕ} (s : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) (ν : E) (l : F) :
    actU (GlobalTheory.JR.Step.uEmb r E s) (GlobalTheory.JR.Step.liftH X ν l) = GlobalTheory.JR.Step.liftH (actU s X) ν l := by
  have hs : star (embHom r E s.1) = embHom r E (star s.1) := by
    simp only [embHom, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.star_eq_conjTranspose, Matrix.reindex_apply,
      Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      Matrix.conjTranspose_one]
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · apply Subtype.ext
    show embHom r E s.1 * full X.toGl * star (embHom r E s.1) = full (actU s X).toGl
    rw [hs]
    simp only [embHom, full, Hn.toGl, actU, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.reindex_apply,
      Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    congr 2
    all_goals (ext i j; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.vecMul, Finset.sum_apply, star_sum, mul_comm, Matrix.star_apply])
  · show embHom r E s.1 *ᵥ (ν • eL r E) = ν • eL r E
    ext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [embHom, eL, Matrix.mulVec, dotProduct, Matrix.reindex_apply, Fin.sum_univ_castSucc]
    · simp [embHom, eL, Matrix.mulVec, dotProduct, Matrix.reindex_apply, Fin.sum_univ_castSucc]

end GlobalTheory.JR.Step
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryActHermitianBlockDiagOneLiftLastBasisStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryActHermitianBlock_diagOne_liftLastBasis : ∀ {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] {r : ℕ} (s : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) (ν : E) (l : F), actU (GlobalTheory.JR.Step.uEmb r E s) (GlobalTheory.JR.Step.liftH X ν l) = GlobalTheory.JR.Step.liftH (actU s X) ν l := by
  first | exact @GlobalTheory.JR.Step.actU_uEmb_liftH | exact GlobalTheory.JR.Step.actU_uEmb_liftH | (intros; apply GlobalTheory.JR.Step.actU_uEmb_liftH <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitIndicatorHermitianBlockLiftLastBasisOfNormLe
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitIndicatorHermitianBlockLiftLastBasisOfNormLe
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Step

theorem forall_full_entries_iff {r : ℕ} {k : Type} [CommRing k] (Y : Gl r k) (P : k → Prop) :
    (∀ i j, P (full Y i j)) ↔
      (∀ i j, P (Y.1 i j)) ∧ (∀ i, P (Y.2.1 i)) ∧ (∀ j, P (Y.2.2.1 j)) ∧ P Y.2.2.2 := by
  constructor
  · intro h
    refine ⟨fun i j => ?_, fun i => ?_, fun j => ?_, ?_⟩
    · simpa [full] using h (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j))
    · simpa [full] using h (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr (0 : Fin 1)))
    · simpa [full] using h (finSumFinEquiv (Sum.inr (0 : Fin 1))) (finSumFinEquiv (Sum.inl j))
    · simpa [full] using h (finSumFinEquiv (Sum.inr (0 : Fin 1))) (finSumFinEquiv (Sum.inr (0 : Fin 1)))
  · rintro ⟨h1, h2, h3, h4⟩ i j
    simp only [full, Matrix.reindex_apply, Matrix.submatrix_apply]
    rcases finSumFinEquiv.symm i with a | a <;> rcases finSumFinEquiv.symm j with b | b
    · simpa using h1 a b
    · simpa using h2 a
    · simpa using h3 b
    · simpa using h4

theorem unitU_liftH_of_norm_le_one {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] {r : ℕ} (X : Hn r F E) (ν : E) (l : F) (hν : ‖ν‖ ≤ 1) :
    unitU (r + 1) F E (liftH X ν l) = (if ‖l‖ ≤ 1 then 1 else 0) * unitU r F E X := by
  classical
  have hA : (∀ i j, ‖full X.toGl i j‖ ≤ 1) ↔
      (∀ i j, ‖X.1.1 i j‖ ≤ 1) ∧ (∀ i, ‖X.2.1 i‖ ≤ 1) ∧ ‖X.2.2‖ ≤ 1 := by
    rw [forall_full_entries_iff X.toGl (fun x => ‖x‖ ≤ 1)]
    simp only [Hn.toGl, Pi.star_apply, Unram.norm_star (F := F), norm_algebraMap']
    tauto
  have hb : ∀ i, ‖(ν • eL r E) i‖ ≤ 1 := by
    intro i
    by_cases hi : i = Fin.last r
    · subst hi; simpa [eL] using hν
    · simp [eL, Pi.single_eq_of_ne hi]
  unfold unitU
  simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
  have e : ((∀ i j, ‖(liftH X ν l).1.1 i j‖ ≤ 1) ∧ (∀ i, ‖(liftH X ν l).2.1 i‖ ≤ 1) ∧ ‖(liftH X ν l).2.2‖ ≤ 1) ↔
      (‖l‖ ≤ 1 ∧ (∀ i j, ‖X.1.1 i j‖ ≤ 1) ∧ (∀ i, ‖X.2.1 i‖ ≤ 1) ∧ ‖X.2.2‖ ≤ 1) := by
    change ((∀ i j, ‖full X.toGl i j‖ ≤ 1) ∧ (∀ i, ‖(ν • eL r E) i‖ ≤ 1) ∧ ‖l‖ ≤ 1) ↔ _
    rw [hA]
    exact ⟨fun h => ⟨h.2.2, h.1⟩, fun h => ⟨h.2, hb, h.1⟩⟩
  simp only [e]
  by_cases h1 : ‖l‖ ≤ 1 <;>
    by_cases h2 : (∀ i j, ‖X.1.1 i j‖ ≤ 1) ∧ (∀ i, ‖X.2.1 i‖ ≤ 1) ∧ ‖X.2.2‖ ≤ 1 <;>
    simp only [h1, h2, if_true, if_false, true_and, false_and, and_self, mul_one, mul_zero, zero_mul, implies_true]

end GlobalTheory.JR.Step
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitIndicatorHermitianBlockLiftLastBasisOfNormLeStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitIndicatorHermitianBlock_liftLastBasis_of_norm_le_one : ∀ {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] {r : ℕ} (X : Hn r F E) (ν : E) (l : F), ‖ν‖ ≤ 1 → unitU (r + 1) F E (GlobalTheory.JR.Step.liftH X ν l) = (if ‖l‖ ≤ 1 then 1 else 0) * unitU r F E X := by
  first | exact @GlobalTheory.JR.Step.unitU_liftH_of_norm_le_one | exact GlobalTheory.JR.Step.unitU_liftH_of_norm_le_one | (intros; apply GlobalTheory.JR.Step.unitU_liftH_of_norm_le_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsClosedEmbeddingDiagOneUnitaryGroupEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsClosedEmbeddingDiagOneUnitaryGroupEmbedding
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Step

theorem isClosedEmbedding_embHom (r : ℕ) (E : Type) [CommRing E] [TopologicalSpace E] [T2Space E] :
    Topology.IsClosedEmbedding (embHom r E) := by
  have hc : Continuous (embHom r E) := by
    change Continuous fun g : Matrix (Fin r) (Fin r) E =>
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g 0 0 (1 : Matrix (Fin 1) (Fin 1) E))
    exact (continuous_id.matrix_fromBlocks continuous_const continuous_const continuous_const).matrix_reindex _ _
  have hl : Function.LeftInverse
      (fun M : Matrix (Fin (r + 1)) (Fin (r + 1)) E => M.submatrix (Fin.castAdd 1) (Fin.castAdd 1))
      (embHom r E) := by
    intro g
    ext i j
    change (Matrix.fromBlocks g 0 0 (1 : Matrix (Fin 1) (Fin 1) E))
      (finSumFinEquiv.symm (Fin.castAdd 1 i)) (finSumFinEquiv.symm (Fin.castAdd 1 j)) = g i j
    rw [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_castAdd]
    rfl
  exact hl.isClosedEmbedding (continuous_id.matrix_submatrix _ _) hc

theorem isClosed_unitaryGroup (r : ℕ) (E : Type) [NormedField E] [StarRing E] [ContinuousStar E] :
    IsClosed (Matrix.unitaryGroup (Fin r) E : Set (Matrix (Fin r) (Fin r) E)) := by
  have : (Matrix.unitaryGroup (Fin r) E : Set (Matrix (Fin r) (Fin r) E)) = {M | M * Mᴴ = 1} := by
    ext M
    exact Matrix.mem_unitaryGroup_iff
  rw [this]
  exact isClosed_eq (continuous_id.matrix_mul continuous_id.matrix_conjTranspose) continuous_const

theorem isClosedEmbedding_uEmb (r : ℕ) (E : Type) [NormedField E] [StarRing E] [ContinuousStar E] :
    Topology.IsClosedEmbedding (GlobalTheory.JR.Step.uEmb r E) := by
  have h1 : Topology.IsClosedEmbedding
      (Subtype.val : Matrix.unitaryGroup (Fin (r + 1)) E → Matrix (Fin (r + 1)) (Fin (r + 1)) E) :=
    (isClosed_unitaryGroup (r + 1) E).isClosedEmbedding_subtypeVal
  have h0 : Topology.IsClosedEmbedding
      (Subtype.val : Matrix.unitaryGroup (Fin r) E → Matrix (Fin r) (Fin r) E) :=
    (isClosed_unitaryGroup r E).isClosedEmbedding_subtypeVal
  rw [← h1.of_comp_iff]
  exact (isClosedEmbedding_embHom r E).comp h0

end GlobalTheory.JR.Step
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsClosedEmbeddingDiagOneUnitaryGroupEmbeddingStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosedEmbedding_diagOneUnitaryGroupEmbedding : ∀ (r : ℕ) (E : Type) [NormedField E] [StarRing E] [ContinuousStar E], Topology.IsClosedEmbedding (GlobalTheory.JR.Step.uEmb r E) := by
  first | exact @GlobalTheory.JR.Step.isClosedEmbedding_uEmb | exact GlobalTheory.JR.Step.isClosedEmbedding_uEmb | (intros; apply GlobalTheory.JR.Step.isClosedEmbedding_uEmb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryOrbitalIntegralLiftLastBasisReduce
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Step.OrbULift
theorem actU_uEmb_liftH : ∀ {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] {r : ℕ} (s : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) (ν : E) (l : F), actU (GlobalTheory.JR.Step.uEmb r E s) (GlobalTheory.JR.Step.liftH X ν l) = GlobalTheory.JR.Step.liftH (actU s X) ν l := GlobalTheory.T.unitaryActHermitianBlock_diagOne_liftLastBasis
theorem unitU_liftH : ∀ {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] {r : ℕ} (X : Hn r F E) (ν : E) (l : F), ‖ν‖ ≤ 1 → unitU (r + 1) F E (GlobalTheory.JR.Step.liftH X ν l) = (if ‖l‖ ≤ 1 then 1 else 0) * unitU r F E X := GlobalTheory.T.unitIndicatorHermitianBlock_liftLastBasis_of_norm_le_one
theorem support_sub : ∀ {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] {r : ℕ} (X : Hn r F E) (ν : E) (l : F), ‖ν‖ = 1 → ∀ g : Matrix.unitaryGroup (Fin (r + 1)) E, unitU (r + 1) F E (actU g (GlobalTheory.JR.Step.liftH X ν l)) ≠ 0 → ∃ k ∈ uO (r + 1) E, ∃ s, g = k * GlobalTheory.JR.Step.uEmb r E s := GlobalTheory.T.unitaryAct_liftHermitianBlock_mem_integralUnitary_mul_embedding
theorem support_bounded : ∀ {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] {n : ℕ} (Y : Hn n F E), Delta (inv Y.toGl) ≠ 0 → ∃ K : Set (Matrix.unitaryGroup (Fin n) E), IsCompact K ∧ ∀ g, unitU n F E (actU g Y) ≠ 0 → g ∈ K := GlobalTheory.T.exists_compact_unitaries_integral_orbit_of_hankelDet_ne_zero
theorem uEmb_isClosedEmbedding : ∀ (r : ℕ) (E : Type) [NormedField E] [StarRing E] [ContinuousStar E], Topology.IsClosedEmbedding (GlobalTheory.JR.Step.uEmb r E) := GlobalTheory.T.isClosedEmbedding_diagOneUnitaryGroupEmbedding

section Reformulated
variable {E : Type} [NormedField E]

theorem entries_mul_le {n : ℕ} [IsUltrametricDist E] {P Q : Matrix (Fin n) (Fin n) E}
    (hP : ∀ i j, ‖P i j‖ ≤ 1) (hQ : ∀ i j, ‖Q i j‖ ≤ 1) : ∀ i j, ‖(P * Q) i j‖ ≤ 1 := by
  intro i j
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hP i k) (norm_nonneg _) (hQ k j)

theorem entries_mulVec_le {n : ℕ} [IsUltrametricDist E] {P : Matrix (Fin n) (Fin n) E} {v : Fin n → E}
    (hP : ∀ i j, ‖P i j‖ ≤ 1) (hv : ∀ i, ‖v i‖ ≤ 1) : ∀ i, ‖(P *ᵥ v) i‖ ≤ 1 := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hP i k) (norm_nonneg _) (hv k)

variable [StarRing E]

theorem entries_star_le {n : ℕ} [NormedStarGroup E] {P : Matrix (Fin n) (Fin n) E}
    (hP : ∀ i j, ‖P i j‖ ≤ 1) : ∀ i j, ‖(star P) i j‖ ≤ 1 := by
  intro i j
  rw [Matrix.star_apply, norm_star]
  exact hP j i

theorem uO_mul {n : ℕ} [IsUltrametricDist E]
    {a b : Matrix.unitaryGroup (Fin n) E} (ha : a ∈ uO n E) (hb : b ∈ uO n E) : a * b ∈ uO n E :=
  entries_mul_le (P := a.1) (Q := b.1) ha hb

theorem uO_one {n : ℕ} : (1 : Matrix.unitaryGroup (Fin n) E) ∈ uO n E := by
  intro i j
  show ‖(1 : Matrix (Fin n) (Fin n) E) i j‖ ≤ 1
  rw [Matrix.one_apply]
  split_ifs <;> simp

theorem uO_inv {n : ℕ} [NormedStarGroup E]
    {a : Matrix.unitaryGroup (Fin n) E} (ha : a ∈ uO n E) : a⁻¹ ∈ uO n E :=
  entries_star_le (P := a.1) ha

theorem uO_isOpen {n : ℕ} [IsUltrametricDist E] : IsOpen (uO n E) := by
  have e : uO n E = ⋂ i, ⋂ j, (fun g : Matrix.unitaryGroup (Fin n) E => g.1 i j) ⁻¹' Metric.closedBall 0 1 := by
    ext g; simp [uO]
  rw [e]
  have hc : ∀ i j, Continuous (fun g : Matrix.unitaryGroup (Fin n) E => g.1 i j) := fun i j =>
    (continuous_subtype_val (p := fun M => M ∈ Matrix.unitaryGroup (Fin n) E)).matrix_elem i j
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (IsUltrametricDist.isOpen_closedBall (0 : E) one_ne_zero).preimage (hc i j)

theorem isClosed_unitaryGroup' {n : ℕ} [ContinuousStar E] :
    IsClosed (Matrix.unitaryGroup (Fin n) E : Set (Matrix (Fin n) (Fin n) E)) := by
  have e : (Matrix.unitaryGroup (Fin n) E : Set (Matrix (Fin n) (Fin n) E)) = {M | star M * M = 1} := by
    ext M; exact Matrix.mem_unitaryGroup_iff'
  rw [e]
  exact isClosed_eq (continuous_star.matrix_mul continuous_id) continuous_const

theorem uO_isCompact {n : ℕ} [ProperSpace E] [ContinuousStar E] : IsCompact (uO n E) := by
  let B : Set (Matrix (Fin n) (Fin n) E) :=
    Set.univ.pi fun _ => Set.univ.pi fun _ => Metric.closedBall (0 : E) 1
  have hB : IsCompact B := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  have e : uO n E = Subtype.val ⁻¹' B := by
    ext g
    show (∀ i j, ‖g.1 i j‖ ≤ 1) ↔
      (∀ i ∈ (Set.univ : Set (Fin n)), ∀ j ∈ (Set.univ : Set (Fin n)), g.1 i j ∈ Metric.closedBall (0 : E) 1)
    simp
  rw [e]
  exact (isClosed_unitaryGroup' (n := n)).isClosedEmbedding_subtypeVal.isCompact_preimage hB

theorem preimage_uO (r : ℕ) : uEmb r E ⁻¹' uO (r + 1) E = uO r E := by
  ext s
  simp only [Set.mem_preimage, uO, Set.mem_setOf_eq]
  constructor
  · intro h i j
    have := h (Fin.castSucc i) (Fin.castSucc j)
    simpa [uEmb, embHom, Matrix.reindex_apply] using this
  · intro h i j
    show ‖(embHom r E s.1) i j‖ ≤ 1
    simp only [embHom, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.reindex_apply, Matrix.submatrix_apply]
    generalize finSumFinEquiv.symm i = a
    generalize finSumFinEquiv.symm j = b
    rcases a with a | a <;> rcases b with b | b
    · simpa using h a b
    · simp
    · simp
    · rw [Matrix.fromBlocks_apply₂₂, Matrix.one_apply]; split_ifs <;> simp

theorem actU_mul {F : Type} [CommRing F] [Algebra F E] {n : ℕ} (k g : Matrix.unitaryGroup (Fin n) E)
    (Y : Hn n F E) : actU (k * g) Y = actU k (actU g Y) := by
  unfold actU
  refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ rfl)
  · show (k.1 * g.1) * Y.1.1 * star (k.1 * g.1) = k.1 * (g.1 * Y.1.1 * star g.1) * star k.1
    rw [star_mul]; simp only [Matrix.mul_assoc]
  · show (k.1 * g.1) *ᵥ Y.2.1 = k.1 *ᵥ (g.1 *ᵥ Y.2.1)
    rw [Matrix.mulVec_mulVec]

theorem actU_one {F : Type} [CommRing F] [Algebra F E] {n : ℕ} (Y : Hn n F E) :
    actU (1 : Matrix.unitaryGroup (Fin n) E) Y = Y := by
  unfold actU
  refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ rfl)
  · show (1 : Matrix (Fin n) (Fin n) E) * Y.1.1 * star (1 : Matrix (Fin n) (Fin n) E) = Y.1.1
    simp
  · show (1 : Matrix (Fin n) (Fin n) E) *ᵥ Y.2.1 = Y.2.1
    simp

theorem integral_actU {F : Type} [NormedField F] [Algebra F E] [IsUltrametricDist E] [NormedStarGroup E] {n : ℕ}
    (k : Matrix.unitaryGroup (Fin n) E) (hk : k ∈ uO n E) (Y : Hn n F E)
    (hY : Y ∈ {X : Hn n F E | (∀ i j, ‖X.1.1 i j‖ ≤ 1) ∧ (∀ i, ‖X.2.1 i‖ ≤ 1) ∧ ‖X.2.2‖ ≤ 1}) :
    actU k Y ∈ {X : Hn n F E | (∀ i j, ‖X.1.1 i j‖ ≤ 1) ∧ (∀ i, ‖X.2.1 i‖ ≤ 1) ∧ ‖X.2.2‖ ≤ 1} := by
  obtain ⟨h1, h2, h3⟩ := hY
  refine ⟨?_, ?_, h3⟩
  · exact entries_mul_le (entries_mul_le hk h1) (entries_star_le hk)
  · exact entries_mulVec_le hk h2

end Reformulated

theorem unitU_actU_mul {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [IsUltrametricDist E] [NormedStarGroup E] {n : ℕ} (k g : Matrix.unitaryGroup (Fin n) E) (hk : k ∈ uO n E)
    (Y : Hn n F E) : unitU n F E (actU (k * g) Y) = unitU n F E (actU g Y) := by
  rw [actU_mul]
  have hiff : ∀ Z : Hn n F E, actU k Z ∈ {X : Hn n F E | (∀ i j, ‖X.1.1 i j‖ ≤ 1) ∧ (∀ i, ‖X.2.1 i‖ ≤ 1) ∧ ‖X.2.2‖ ≤ 1} ↔
      Z ∈ {X : Hn n F E | (∀ i j, ‖X.1.1 i j‖ ≤ 1) ∧ (∀ i, ‖X.2.1 i‖ ≤ 1) ∧ ‖X.2.2‖ ≤ 1} := fun Z =>
    ⟨fun h => by
      have := integral_actU k⁻¹ (uO_inv hk) _ h
      rwa [← actU_mul, inv_mul_cancel, actU_one] at this, fun h => integral_actU k hk Z h⟩
  unfold unitU
  by_cases h : actU g Y ∈ {X : Hn n F E | (∀ i j, ‖X.1.1 i j‖ ≤ 1) ∧ (∀ i, ‖X.2.1 i‖ ≤ 1) ∧ ‖X.2.2‖ ≤ 1}
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((hiff _).2 h)]; rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((hiff _).1 h'))]

theorem compact_support {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] {r : ℕ} (X : Hn r F E) (ν : E) (l : F)
    (hΔ : Delta (inv (liftH X ν l).toGl) ≠ 0) :
    HasCompactSupport (fun s => unitU (r + 1) F E (actU (uEmb r E s) (liftH X ν l))) := by
  haveI : NormedStarGroup E := ⟨fun x => (Unram.norm_star (F := F) x).le⟩
  obtain ⟨K, hK, hsub⟩ := support_bounded (liftH X ν l) hΔ
  refine HasCompactSupport.intro ((uEmb_isClosedEmbedding r E).isCompact_preimage hK) ?_
  intro s hs
  by_contra h
  exact hs (hsub _ h)

theorem orbU_liftH (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas (r + 1) F E) (M' : Meas r F E) (X : Hn r F E) (ν : E) (l : F) (hν : ‖ν‖ = 1) (hΔ : Delta (inv (GlobalTheory.JR.Step.liftH X ν l).toGl) ≠ 0) :
  orbU M (unitU (r + 1) F E) (GlobalTheory.JR.Step.liftH X ν l) = (if ‖l‖ ≤ 1 then 1 else 0) * orbU M' (unitU r F E) X := by
  haveI : IsUltrametricDist E := Unram.ultraE (F := F)
  haveI : NormedStarGroup E := ⟨fun x => (Unram.norm_star (F := F) x).le⟩
  haveI : LocallyCompactSpace E := Unram.lcE (F := F)
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : SecondCountableTopology (Matrix (Fin (r+1)) (Fin (r+1)) E) :=
    inferInstanceAs (SecondCountableTopology (Fin (r+1) → Fin (r+1) → E))
  haveI : SecondCountableTopology (Matrix.unitaryGroup (Fin (r+1)) E) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : LocallyCompactSpace (Matrix.unitaryGroup (Fin (r+1)) E) := by
    exact IsCompact.locallyCompactSpace_of_mem_nhds_of_group (uO_isCompact (n := r + 1))
      (uO_isOpen.mem_nhds uO_one)
  let R₀ : Subgroup (Matrix.unitaryGroup (Fin (r+1)) E) :=
    { carrier := uO (r+1) E, mul_mem' := uO_mul, one_mem' := uO_one, inv_mem' := uO_inv }
  unfold orbU
  letI := M.mU; haveI := M.bU; letI := M'.mU; haveI := M'.bU
  haveI := M.haarU; haveI := M'.haarU
  haveI := (GlobalTheory.T.unitaryGroup_positiveCharacter_trivial_and_unimodular F E (r+1)).2 M
  haveI := (GlobalTheory.T.unitaryGroup_positiveCharacter_trivial_and_unimodular F E r).2 M'
  rw [GlobalTheory.CosetIntegral.integral_eq_of_coset_support _ _ (uEmb r E) (uEmb_isClosedEmbedding r E) M.μU M'.μU R₀
    uO_isOpen uO_isCompact M.volU (by
      show M'.μU (uEmb r E ⁻¹' uO (r + 1) E) = 1
      rw [preimage_uO]; exact M'.volU)
    _ (fun k hk g => unitU_actU_mul k g hk _) (support_sub X ν l hν) (compact_support X ν l hΔ)]
  simp_rw [actU_uEmb_liftH, unitU_liftH _ ν l hν.le]
  rw [integral_const_mul]
end GlobalTheory.JR.Step.OrbULift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryOrbitalIntegralLiftLastBasisReduceStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryOrbitalIntegral_liftLastBasis_reduce : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas (r + 1) F E) (M' : Meas r F E) (X : Hn r F E) (ν : E) (l : F), ‖ν‖ = 1 → Delta (inv (GlobalTheory.JR.Step.liftH X ν l).toGl) ≠ 0 → orbU M (unitU (r + 1) F E) (GlobalTheory.JR.Step.liftH X ν l) = (if ‖l‖ ≤ 1 then 1 else 0) * orbU M' (unitU r F E) X := by
  first | exact @GlobalTheory.JR.Step.OrbULift.orbU_liftH | exact GlobalTheory.JR.Step.OrbULift.orbU_liftH | (intros; apply GlobalTheory.JR.Step.OrbULift.orbU_liftH <;> assumption)
end
