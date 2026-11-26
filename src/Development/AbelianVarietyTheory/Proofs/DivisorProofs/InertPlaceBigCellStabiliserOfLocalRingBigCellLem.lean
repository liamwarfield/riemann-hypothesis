module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnimodularFrameInertPlace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertCompletionToAdelesProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertCompletionToAdelesProperties
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.InertBigCell

theorem iotaW_adelic_place : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {v : Pl (F := F)}
    {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w),
  Function.Injective (GlobalTheory.InertBigCell.iotaW hw) ∧
  (∀ x y, GlobalTheory.InertBigCell.iotaW hw (x * y) = GlobalTheory.InertBigCell.iotaW hw x * GlobalTheory.InertBigCell.iotaW hw y) ∧
  GlobalTheory.InertBigCell.iotaW hw 1 = algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) ∧
  (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ↔ ∃ x, GlobalTheory.InertBigCell.iotaW hw x = z) ∧
  (∀ x, GlobalTheory.InertBigCell.iotaW hw (GlobalTheory.InertBigCell.conjW σ hw x) = cA σ (GlobalTheory.InertBigCell.iotaW hw x)) ∧
  (∀ x, GlobalTheory.InertBigCell.iotaW hw (2⁻¹ * x) = ⅟(2 : AF F) • GlobalTheory.InertBigCell.iotaW hw x) ∧
  (∀ e : E, GlobalTheory.InertBigCell.iotaW hw (algebraMap E (w.adicCompletion E) e) =
    algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) * inclR (F := F) (AF F) e) := by
  intro F E _ _ _ _ _ σ v w hw
  refine ⟨iotaW_injective hw, iotaW_mul hw, iotaW_one hw, fun z => ?_, iotaW_conjW σ hw, fun x => ?_,
    iotaW_algebraMap hw⟩
  · rw [GlobalTheory.InertLocField.at_iff v z]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨InertChart.complEquiv hw (under_eq_of_isInertAt hw) y, by
        rw [iotaW_apply, RingEquiv.symm_apply_apply]⟩
    · rintro ⟨x, rfl⟩
      exact ⟨_, (iotaW_apply hw x).symm⟩
  · have h := invOf_two_smul_add_iotaW hw 0 x
    rw [add_zero, zero_add, zero_add] at h
    exact h.symm

end GlobalTheory.InertBigCell
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertCompletionToAdelesPropertiesStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertCompletionToAdeles_properties : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {v : Pl (F := F)}
    {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w),
  Function.Injective (GlobalTheory.InertBigCell.iotaW hw) ∧
  (∀ x y, GlobalTheory.InertBigCell.iotaW hw (x * y) = GlobalTheory.InertBigCell.iotaW hw x * GlobalTheory.InertBigCell.iotaW hw y) ∧
  GlobalTheory.InertBigCell.iotaW hw 1 = algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) ∧
  (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ↔ ∃ x, GlobalTheory.InertBigCell.iotaW hw x = z) ∧
  (∀ x, GlobalTheory.InertBigCell.iotaW hw (GlobalTheory.InertBigCell.conjW σ hw x) = cA σ (GlobalTheory.InertBigCell.iotaW hw x)) ∧
  (∀ x, GlobalTheory.InertBigCell.iotaW hw (2⁻¹ * x) = ⅟(2 : AF F) • GlobalTheory.InertBigCell.iotaW hw x) ∧
  (∀ e : E, GlobalTheory.InertBigCell.iotaW hw (algebraMap E (w.adicCompletion E) e) =
    algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) * inclR (F := F) (AF F) e) := by
  first | exact @GlobalTheory.InertBigCell.iotaW_adelic_place | exact GlobalTheory.InertBigCell.iotaW_adelic_place | (intros; apply GlobalTheory.InertBigCell.iotaW_adelic_place <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMatrixGluedAtInertPlaceProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMatrixGluedAtInertPlaceProperties
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertBigCell

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)}

theorem gl_iotaW_apply (hw : Formalism.UG.IsInertAt F E v w) (x : w.adicCompletion E) :
    iotaW hw x = GlobalTheory.InertLocField.liftT E v ((InertChart.complEquiv hw (under_eq_of_isInertAt hw)).symm x) := rfl

theorem gl_iotaW_mul (hw : Formalism.UG.IsInertAt F E v w) (x y : w.adicCompletion E) :
    iotaW hw (x * y) = iotaW hw x * iotaW hw y := by
  rw [gl_iotaW_apply, gl_iotaW_apply, gl_iotaW_apply, map_mul, GlobalTheory.InertLocField.liftT_mul]

theorem gl_iotaW_injective (hw : Formalism.UG.IsInertAt F E v w) : Function.Injective (iotaW hw) := fun x y hxy =>
  (InertChart.complEquiv hw (under_eq_of_isInertAt hw)).symm.injective (GlobalTheory.InertLocField.liftT_injective v hxy)

theorem gl_idem_mul_iotaW (hw : Formalism.UG.IsInertAt F E v w) (x : w.adicCompletion E) :
    algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) * iotaW hw x = iotaW hw x := by
  rw [← Algebra.smul_def, GlobalTheory.InertLocField.liftV_one_smul, gl_iotaW_apply, GlobalTheory.InertLocField.evT_liftT]

theorem gl_iotaW_one (hw : Formalism.UG.IsInertAt F E v w) :
    iotaW hw 1 = algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) := by
  have h := GlobalTheory.InertLocField.liftV_one_smul (E := E) v 1
  rw [Algebra.smul_def, mul_one, _root_.map_one (GlobalTheory.InertLocField.evT E v)] at h
  rw [gl_iotaW_apply, _root_.map_one]
  exact h.symm

theorem gl_compl_mul_iotaW (hw : Formalism.UG.IsInertAt F E v w) (x : w.adicCompletion E) :
    (1 - algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1)) * iotaW hw x = 0 := by
  rw [sub_mul, one_mul, gl_idem_mul_iotaW, sub_self]

theorem gl_compl_idem (hw : Formalism.UG.IsInertAt F E v w) :
    (1 - algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1)) * (1 - algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1)) =
      1 - algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) := by
  have h := gl_idem_mul_iotaW hw 1
  rw [gl_iotaW_one] at h
  rw [mul_sub, mul_one, sub_mul, one_mul, h, sub_self, sub_zero]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem gl_compl_smul_map (hw : Formalism.UG.IsInertAt F E v w) (P : Matrix ι ι (w.adicCompletion E)) :
    (1 - algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1)) • P.map (iotaW hw) = 0 := by
  ext i j
  rw [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, gl_compl_mul_iotaW, Matrix.zero_apply]

theorem gl_map_mul_map (hw : Formalism.UG.IsInertAt F E v w) (P Q : Matrix ι ι (w.adicCompletion E)) :
    P.map (iotaW hw) * Q.map (iotaW hw) = (P * Q).map (iotaW hw) := by
  ext i k
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.mul_apply, Matrix.map_apply, Matrix.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.map_apply, Matrix.map_apply, gl_iotaW_mul]

theorem gl_map_one_eq (hw : Formalism.UG.IsInertAt F E v w) :
    (1 : Matrix ι ι (w.adicCompletion E)).map (iotaW hw) =
      algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) • (1 : Matrix ι ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := by
  ext i j
  rw [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · rw [gl_iotaW_one, smul_eq_mul, mul_one]
  · rw [map_zero, smul_zero]

theorem gl_glueW_sub_one (hw : Formalism.UG.IsInertAt F E v w) (P : Matrix ι ι (w.adicCompletion E)) :
    glueW hw P - 1 = (P - 1).map (iotaW hw) := by
  rw [Matrix.map_sub _ (map_sub (iotaW hw)), gl_map_one_eq, glueW, sub_smul, one_smul]
  abel

theorem glueW_props : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl (F := F)}
    {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w) {ι : Type} [Fintype ι] [DecidableEq ι],
  (∀ P Q : Matrix ι ι (w.adicCompletion E), GlobalTheory.InertBigCell.glueW hw (P * Q) = GlobalTheory.InertBigCell.glueW hw P * GlobalTheory.InertBigCell.glueW hw Q) ∧
  GlobalTheory.InertBigCell.glueW hw (1 : Matrix ι ι (w.adicCompletion E)) = 1 ∧
  Function.Injective (GlobalTheory.InertBigCell.glueW hw (ι := ι)) ∧
  (∀ P : Matrix ι ι (w.adicCompletion E), At (evFin F v) (GlobalTheory.InertBigCell.glueW hw P - 1)) ∧
  (∀ M : Matrix ι ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) (M - 1) → ∃ P, GlobalTheory.InertBigCell.glueW hw P = M) ∧
  (∀ (P : Matrix ι ι (w.adicCompletion E)) (u : ι → w.adicCompletion E),
    GlobalTheory.InertBigCell.glueW hw P *ᵥ (fun i => GlobalTheory.InertBigCell.iotaW hw (u i)) = fun i => GlobalTheory.InertBigCell.iotaW hw ((P *ᵥ u) i)) := by
  intro F E _ _ _ _ _ v w hw ι _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro P Q
    have h1 : ∀ B : Matrix ι ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), ((1 - algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1)) • (1 : Matrix ι ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) * B =
        (1 - algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1)) • B := fun B => by
      rw [Matrix.smul_mul, Matrix.one_mul]
    have h2 : ∀ A : Matrix ι ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), A * ((1 - algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1)) • (1 : Matrix ι ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) =
        (1 - algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1)) • A := fun A => by
      rw [Matrix.mul_smul, Matrix.mul_one]
    rw [glueW, glueW, glueW, add_mul, mul_add, mul_add, h1, h1, h2, smul_smul, gl_compl_idem hw, gl_compl_smul_map,
      gl_compl_smul_map, gl_map_mul_map, add_zero, zero_add]
  · rw [glueW, gl_map_one_eq, ← add_smul, sub_add_cancel, one_smul]
  · intro P Q hPQ
    have h : P.map (iotaW hw) = Q.map (iotaW hw) := add_left_cancel hPQ
    exact Matrix.ext fun i j => gl_iotaW_injective hw (congrFun (congrFun h i) j)
  · intro P u hu
    rw [gl_glueW_sub_one]
    ext i j
    rw [Matrix.smul_apply, Matrix.map_apply, Matrix.zero_apply, gl_iotaW_apply]
    exact GlobalTheory.InertLocField.at_liftT v _ u hu
  · intro M hM
    have hent : ∀ i j, ∃ y, GlobalTheory.InertLocField.liftT E v y = (M - 1) i j := fun i j =>
      (GlobalTheory.InertLocField.at_iff v _).1 (fun u hu => by
        have := congrFun (congrFun (hM u hu) i) j
        rwa [Matrix.smul_apply] at this)
    choose y hy using hent
    refine ⟨1 + Matrix.of fun i j => InertChart.complEquiv hw (under_eq_of_isInertAt hw) (y i j), ?_⟩
    have hX : (Matrix.of fun i j => InertChart.complEquiv hw (under_eq_of_isInertAt hw) (y i j)).map (iotaW hw) = M - 1 := by
      ext i j
      rw [Matrix.map_apply, Matrix.of_apply, gl_iotaW_apply, RingEquiv.symm_apply_apply, hy]
    have h := gl_glueW_sub_one hw (1 + Matrix.of fun i j => InertChart.complEquiv hw (under_eq_of_isInertAt hw) (y i j))
    rw [add_sub_cancel_left, hX] at h
    exact sub_left_inj.mp h
  · intro P u
    have hd : ∀ x : ι → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), ((1 - algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1)) • (1 : Matrix ι ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) *ᵥ x =
        (1 - algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1)) • x := fun x => by
      funext i
      simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [glueW, Matrix.add_mulVec, hd, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      gl_compl_mul_iotaW, zero_add, Matrix.mulVec, dotProduct, Matrix.mulVec, dotProduct, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.map_apply, gl_iotaW_mul]

end GlobalTheory.InertBigCell
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMatrixGluedAtInertPlacePropertiesStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicMatrixGluedAtInertPlace_properties : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl (F := F)}
    {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w) {ι : Type} [Fintype ι] [DecidableEq ι],
  (∀ P Q : Matrix ι ι (w.adicCompletion E), GlobalTheory.InertBigCell.glueW hw (P * Q) = GlobalTheory.InertBigCell.glueW hw P * GlobalTheory.InertBigCell.glueW hw Q) ∧
  GlobalTheory.InertBigCell.glueW hw (1 : Matrix ι ι (w.adicCompletion E)) = 1 ∧
  Function.Injective (GlobalTheory.InertBigCell.glueW hw (ι := ι)) ∧
  (∀ P : Matrix ι ι (w.adicCompletion E), At (evFin F v) (GlobalTheory.InertBigCell.glueW hw P - 1)) ∧
  (∀ M : Matrix ι ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) (M - 1) → ∃ P, GlobalTheory.InertBigCell.glueW hw P = M) ∧
  (∀ (P : Matrix ι ι (w.adicCompletion E)) (u : ι → w.adicCompletion E),
    GlobalTheory.InertBigCell.glueW hw P *ᵥ (fun i => GlobalTheory.InertBigCell.iotaW hw (u i)) = fun i => GlobalTheory.InertBigCell.iotaW hw ((P *ᵥ u) i)) := by
  first | exact @GlobalTheory.InertBigCell.glueW_props | exact GlobalTheory.InertBigCell.glueW_props | (intros; apply GlobalTheory.InertBigCell.glueW_props <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceBigCellLocalUnitaryDecomposition
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceBigCellLocalUnitaryDecomposition
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertCellLocal

open Matrix GlobalTheory.InertBigCell

variable {K : Type} [Field K] {d : ℕ}

def wM (b : GL (Fin d) K) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) K :=
  fromBlocks (b : Matrix (Fin d) (Fin d) K) b b (-(b : Matrix (Fin d) (Fin d) K))

def wMi (b : GL (Fin d) K) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) K :=
  (2 : K)⁻¹ • fromBlocks ((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) ((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
    ((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) (-((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K))

lemma two_blocks (h2 : (2 : K) ≠ 0) :
    (2 : K)⁻¹ • fromBlocks (1 + 1 : Matrix (Fin d) (Fin d) K) (0 : Matrix (Fin d) (Fin d) K) (0 : Matrix (Fin d) (Fin d) K) (1 + 1 : Matrix (Fin d) (Fin d) K) = 1 := by
  have : fromBlocks (1 + 1 : Matrix (Fin d) (Fin d) K) (0 : Matrix (Fin d) (Fin d) K) (0 : Matrix (Fin d) (Fin d) K) (1 + 1 : Matrix (Fin d) (Fin d) K) = (2 : K) • fromBlocks (1 : Matrix (Fin d) (Fin d) K) (0 : Matrix (Fin d) (Fin d) K) 0 1 := by
    rw [fromBlocks_smul, smul_zero, ← one_add_one_eq_two, add_smul, one_smul]
  rw [this, smul_smul, inv_mul_cancel₀ h2, one_smul, fromBlocks_one]

lemma wM_mul_wMi (b : GL (Fin d) K) (h2 : (2 : K) ≠ 0) : wM b * wMi b = 1 := by
  have h1 : (b : Matrix (Fin d) (Fin d) K) * ((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := Units.mul_inv b
  simp only [wM, wMi, Matrix.mul_smul, fromBlocks_multiply, h1, neg_mul, mul_neg, neg_neg, add_neg_cancel]
  exact two_blocks h2

lemma wMi_mul_wM (b : GL (Fin d) K) (h2 : (2 : K) ≠ 0) : wMi b * wM b = 1 := by
  have h1 : ((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * (b : Matrix (Fin d) (Fin d) K) = 1 := Units.inv_mul b
  simp only [wM, wMi, Matrix.smul_mul, fromBlocks_multiply, h1, neg_mul, mul_neg, neg_neg, add_neg_cancel]
  exact two_blocks h2

lemma fromBlocks_mul_fromRows_eq {ι κ : Type} [Fintype ι] (A B C D : Matrix ι ι K) (X Y : Matrix ι κ K) :
    fromBlocks A B C D * fromRows X Y = fromRows (A * X + B * Y) (C * X + D * Y) := by
  ext (i | i) j <;> simp [Matrix.mul_apply, Fintype.sum_sum_type]

lemma gram_wM (c : K →+* K) (J : Matrix (Fin d) (Fin d) K) (b : GL (Fin d) K) :
    (wM b)ᵀ * dbl J * (wM b).map c =
      fromBlocks 0 ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c +
          (b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c)
        ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c +
          (b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c) 0 := by
  simp only [wM, dbl, fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, Matrix.transpose_neg,
    Matrix.map_neg _ (map_neg c), Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    neg_neg, Matrix.mul_assoc]
  rw [fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> abel

lemma wMi_diagCols (b : GL (Fin d) K) (h2 : (2 : K) ≠ 0) :
    wMi b * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) K) =
      fromRows ((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) 0 := by
  rw [wMi, show (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) K) = fromRows 1 1 from rfl, Matrix.smul_mul,
    fromBlocks_mul_fromRows_eq]
  simp only [Matrix.mul_one, Matrix.neg_mul, add_neg_cancel]
  ext (i | i) j
  · simp only [Matrix.smul_apply, fromRows_apply_inl, Matrix.add_apply, smul_eq_mul]
    rw [← two_mul, inv_mul_cancel_left₀ h2]
  · simp only [Matrix.smul_apply, fromRows_apply_inr, Matrix.zero_apply, smul_eq_mul, mul_zero]

lemma toBlocks₁₁_conj (b : GL (Fin d) K) (Y : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) K) :
    (wMi b * Y * wM b).toBlocks₁₁ = ((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
      ((2 : K)⁻¹ • (Y.toBlocks₁₁ + Y.toBlocks₁₂ + Y.toBlocks₂₁ + Y.toBlocks₂₂)) * (b : Matrix (Fin d) (Fin d) K) := by
  conv_lhs => rw [← fromBlocks_toBlocks Y]
  have hs : ∀ (r : K) (Z : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) K), (r • Z).toBlocks₁₁ = r • Z.toBlocks₁₁ := fun _ _ => rfl
  simp only [wM, wMi, hs, Matrix.smul_mul, fromBlocks_multiply, toBlocks_fromBlocks₁₁, Matrix.mul_smul,
    Matrix.mul_add, Matrix.add_mul, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, Matrix.smul_apply]
  congr 1
  abel

lemma intMulVec {ι κ : Type} [Fintype κ] (O : ValuationSubring K) (Y : Matrix ι κ K) (v : κ → K)
    (hY : ∀ i j, Y i j ∈ O) (hv : ∀ j, v j ∈ O) : ∀ i, (Y *ᵥ v) i ∈ O :=
  fun i => sum_mem fun j _ => mul_mem (hY i j) (hv j)

lemma inLat2_wM (O : ValuationSubring K) (b : GL (Fin d) K) (y : Fin d ⊕ Fin d → K) (hy : ∀ i, y i ∈ O) :
    InLat2 O b (wM b *ᵥ y) := by
  have h1 : ((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * (b : Matrix (Fin d) (Fin d) K) = 1 := Units.inv_mul b
  refine ⟨fun i => ?_, fun i => ?_⟩ <;>
    simp only [wM, fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.mulVec_add, Matrix.mulVec_mulVec, h1,
      Matrix.one_mulVec, Matrix.neg_mulVec, Matrix.mulVec_neg, Pi.add_apply, Pi.neg_apply]
  · exact add_mem (hy _) (hy _)
  · exact add_mem (hy _) (neg_mem (hy _))

lemma int_wMi (O : ValuationSubring K) (b : GL (Fin d) K) (h2i : (2 : K)⁻¹ ∈ O) (z : Fin d ⊕ Fin d → K)
    (hz : InLat2 O b z) : ∀ i, (wMi b *ᵥ z) i ∈ O := by
  intro i
  rw [wMi, Matrix.smul_mulVec, fromBlocks_mulVec, Pi.smul_apply, smul_eq_mul]
  refine mul_mem h2i ?_
  rcases i with i | i <;>
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.add_apply, Matrix.neg_mulVec, Pi.neg_apply]
  · exact add_mem (hz.1 i) (hz.2 i)
  · exact add_mem (hz.1 i) (neg_mem (hz.2 i))

lemma int_conj_of_keeps (O : ValuationSubring K) (b : GL (Fin d) K) (h2i : (2 : K)⁻¹ ∈ O)
    (Q : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) K) (hQ : ∀ z, InLat2 O b z → InLat2 O b (Q *ᵥ z)) :
    ∀ i j, (wMi b * Q * wM b) i j ∈ O := by
  intro i j
  have he : ∀ k, (Pi.single j (1 : K) : Fin d ⊕ Fin d → K) k ∈ O := by
    intro k
    by_cases hk : k = j
    · subst hk; simp
    · simp [Pi.single_apply, hk]
  have := int_wMi O b h2i _ (hQ _ (inLat2_wM O b _ he)) i
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at this
  exact this

lemma keeps_of_int (O : ValuationSubring K) (b : GL (Fin d) K) (h2i : (2 : K)⁻¹ ∈ O) (h2 : (2 : K) ≠ 0)
    (Q : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) K) (hQ : ∀ i j, (wMi b * Q * wM b) i j ∈ O) :
    ∀ z, InLat2 O b z → InLat2 O b (Q *ᵥ z) := by
  intro z hz
  have h := inLat2_wM O b _ (intMulVec O _ _ hQ (int_wMi O b h2i z hz))
  have e : wM b * (wMi b * Q * wM b) * wMi b = Q := by
    simp only [← Matrix.mul_assoc, wM_mul_wMi b h2, Matrix.one_mul]
    rw [Matrix.mul_assoc, wM_mul_wMi b h2, Matrix.mul_one]
  rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e] at h

lemma conj_form (c : K →+* K) {n : Type} [Fintype n] [DecidableEq n] (W Wi Q D : Matrix n n K) (h1 : W * Wi = 1) :
    (Wi * Q * W)ᵀ * (Wᵀ * D * W.map c) * (Wi * Q * W).map c = Wᵀ * (Qᵀ * D * Q.map c) * W.map c := by
  have e1 : ∀ X : Matrix n n K, Wiᵀ * (Wᵀ * X) = X := by
    intro X; rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, h1, Matrix.transpose_one, Matrix.one_mul]
  have e2 : ∀ X : Matrix n n K, W.map c * (Wi.map c * X) = X := by
    intro X; rw [← Matrix.mul_assoc, ← Matrix.map_mul, h1, Matrix.map_one _ (map_zero c) (map_one c), Matrix.one_mul]
  simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc, e1, e2]

lemma conj_form' (c : K →+* K) {n : Type} [Fintype n] [DecidableEq n] (W Wi U D : Matrix n n K) :
    (W * U * Wi)ᵀ * D * (W * U * Wi).map c = Wiᵀ * (Uᵀ * (Wᵀ * D * W.map c) * U.map c) * Wi.map c := by
  simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]

lemma back_form (c : K →+* K) {n : Type} [Fintype n] [DecidableEq n] (W Wi D : Matrix n n K) (h1 : W * Wi = 1) :
    Wiᵀ * (Wᵀ * D * W.map c) * Wi.map c = D := by
  have e1 : ∀ X : Matrix n n K, Wiᵀ * (Wᵀ * X) = X := by
    intro X; rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, h1, Matrix.transpose_one, Matrix.one_mul]
  have e2 : W.map c * Wi.map c = 1 := by
    rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero c) (map_one c)]
  simp only [Matrix.mul_assoc, e1, e2, Matrix.mul_one]

lemma intU (O : ValuationSubring K) (X : Matrix (Fin d) (Fin d) K) (hX : ∀ i j, X i j ∈ O) :
    ∀ i j, (fromBlocks 1 X 0 1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) K) i j ∈ O := by
  rintro (i | i) (j | j) <;>
    simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.one_apply,
      Matrix.zero_apply]
  · split_ifs <;> simp
  · exact hX i j
  · exact zero_mem O
  · split_ifs <;> simp

end GlobalTheory.InertCellLocal

theorem GlobalTheory.InertCellLocal.bigCell_local_step : (∀ {O : Type} [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) O), IsUnit S.det → Sᵀ = -S.map c →
    ∀ (A B C D : Matrix (Fin n) (Fin n) O), IsUnit (Matrix.fromBlocks A B C D).det →
      (Matrix.fromBlocks A B C D)ᵀ * Matrix.fromBlocks 0 S S 0 * (Matrix.fromBlocks A B C D).map c =
        Matrix.fromBlocks 0 S S 0 →
      ∃ X : Matrix (Fin n) (Fin n) O, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det) →
  ∀ {K : Type} [Field K] (O : ValuationSubring K) (c : K →+* K), (∀ x, c (c x) = x) → (∀ x ∈ O, c x ∈ O) → (2 : K)⁻¹ ∈ O → (2 : K) ≠ 0 →
  ∀ {d : ℕ} (J : Matrix (Fin d) (Fin d) K), Jᵀ = -J.map c →
  ∀ (b : GL (Fin d) K) (δ : K), c δ = δ →
  (∀ i j, (δ • ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c)) i j ∈ O) →
  (δ • ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c)).det ≠ 0 →
  (δ • ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c)).det⁻¹ ∈ O →
  ∀ M M' : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) K, M * M' = 1 → Mᵀ * dbl J * M.map c = dbl J →
  (∀ z, GlobalTheory.InertBigCell.InLat2 O b z → GlobalTheory.InertBigCell.InLat2 O b (M *ᵥ z) ∧ GlobalTheory.InertBigCell.InLat2 O b (M' *ᵥ z)) →
  ∃ P P' : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) K, P * P' = 1 ∧ Pᵀ * dbl J * P.map c = dbl J ∧
    P * diagCols (Fin d) = diagCols (Fin d) ∧
    (∀ z, GlobalTheory.InertBigCell.InLat2 O b z → GlobalTheory.InertBigCell.InLat2 O b (P *ᵥ z) ∧ GlobalTheory.InertBigCell.InLat2 O b (P' *ᵥ z)) ∧
    ∃ N : Matrix (Fin d) (Fin d) K,
      N * ((2 : K)⁻¹ • ((P * M).toBlocks₁₁ + (P * M).toBlocks₁₂ + (P * M).toBlocks₂₁ + (P * M).toBlocks₂₂)) = 1 ∧
      ∀ u, GlobalTheory.InertBigCell.InLat O b u → GlobalTheory.InertBigCell.InLat O b (N *ᵥ u) := open Matrix GlobalTheory.InertBigCell GlobalTheory.InertCellLocal in by
  intro H K _ O c hc hcO h2i h2 d J hJ b δ hδ hG hdet hdeti M M' hMM' hMu hMl

  obtain ⟨cO, hcO'⟩ : ∃ cO : O →+* O, ∀ x, O.subtype (cO x) = c (O.subtype x) :=
    ⟨(c.comp O.subtype).codRestrict O (fun x => hcO x x.2), fun _ => rfl⟩
  have hcOi : ∀ x, cO (cO x) = x := fun x => Subtype.ext (by
    have := hcO' (cO x); rw [hcO' x] at this; exact this.trans (hc _))
  have inj : ∀ {ι κ : Type} {Y Z : Matrix ι κ O}, Y.map O.subtype = Z.map O.subtype → Y = Z :=
    fun h => Matrix.map_injective (fun x y hxy => Subtype.ext hxy) h
  have lift : ∀ {ι κ : Type} (Y : Matrix ι κ K), (∀ i j, Y i j ∈ O) → ∃ Y' : Matrix ι κ O, Y'.map O.subtype = Y :=
    fun Y hY => ⟨fun i j => ⟨Y i j, hY i j⟩, rfl⟩
  have mapc : ∀ {ι κ : Type} (Y : Matrix ι κ O), (Y.map cO).map O.subtype = (Y.map O.subtype).map c := by
    intro ι κ Y; ext i j; simp only [Matrix.map_apply, hcO']
  have hcc : ∀ {ι κ : Type} (Y : Matrix ι κ K), (Y.map c).map c = Y := by
    intro ι κ Y; ext i j; simp only [Matrix.map_apply, hc]
  have smap : ∀ {ι κ : Type} (r : K) (Y : Matrix ι κ K), (r • Y).map c = c r • Y.map c := by
    intro ι κ r Y; ext i j; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  have hWW := wM_mul_wMi b h2
  have hWiW := wMi_mul_wM b h2

  obtain ⟨SO, hSO⟩ := lift _ hG
  have hSOdet : IsUnit SO.det := by
    have e : (SO.det : K) = (δ • ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c)).det := by
      rw [← hSO]; exact RingHom.map_det O.subtype SO
    have h1 : SO.det * ⟨_, hdeti⟩ = 1 := Subtype.ext (by
      show (SO.det : K) * _ = 1
      rw [e, mul_inv_cancel₀ hdet])
    exact ⟨⟨SO.det, ⟨_, hdeti⟩, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  have hGc : ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c).map c =
      ((b : Matrix (Fin d) (Fin d) K).map c)ᵀ * J.map c * (b : Matrix (Fin d) (Fin d) K) := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hcc]
  have hSK : (δ • ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c))ᵀ =
      -(δ • ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c)).map c := by
    rw [smap, hGc, hδ, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hJ]
    simp only [Matrix.neg_mul, Matrix.mul_neg, smul_neg, Matrix.mul_assoc]
  have hSOskew : SOᵀ = -SO.map cO := inj (by
    rw [Matrix.map_neg _ (map_neg O.subtype), mapc, Matrix.transpose_map, hSO, hSK])

  have hMl1 := int_conj_of_keeps O b h2i M (fun z hz => (hMl z hz).1)
  have hMl2 := int_conj_of_keeps O b h2i M' (fun z hz => (hMl z hz).2)
  obtain ⟨g, hg⟩ := lift _ hMl1
  obtain ⟨g', hg'⟩ := lift _ hMl2
  have hgg' : g * g' = 1 := inj (by
    rw [Matrix.map_mul, hg, hg', Matrix.map_one _ (map_zero O.subtype) (map_one O.subtype),
      show wMi b * M * wM b * (wMi b * M' * wM b) = wMi b * (M * (wM b * wMi b) * M') * wM b by
        simp only [Matrix.mul_assoc],
      hWW, Matrix.mul_one, hMM', Matrix.mul_one, hWiW])
  have hdetg : IsUnit g.det := Matrix.isUnit_det_of_right_inverse hgg'
  have hgram := gram_wM c J b
  have hFK : fromBlocks (0 : Matrix (Fin d) (Fin d) K)
      (δ • ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c))
      (δ • ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c)) 0 =
      ((2 : K)⁻¹ * δ) • ((wM b)ᵀ * dbl J * (wM b).map c) := by
    rw [hgram, fromBlocks_smul, smul_zero, ← two_smul K, smul_smul, show (2 : K)⁻¹ * δ * 2 = δ by field_simp]
  have hunitK : (wMi b * M * wM b)ᵀ * ((wM b)ᵀ * dbl J * (wM b).map c) * (wMi b * M * wM b).map c =
      (wM b)ᵀ * dbl J * (wM b).map c := by
    rw [conj_form c (wM b) (wMi b) M (dbl J) hWW, hMu]
  have hunitO : gᵀ * fromBlocks 0 SO SO 0 * g.map cO = fromBlocks 0 SO SO 0 := inj (by
    rw [Matrix.map_mul, Matrix.map_mul, mapc, Matrix.transpose_map, fromBlocks_map,
      Matrix.map_zero _ (map_zero O.subtype), hg, hSO, hFK, Matrix.mul_smul, Matrix.smul_mul, hunitK])
  have h2O : IsUnit (2 : O) := by
    have h1 : (2 : O) * ⟨_, h2i⟩ = 1 := Subtype.ext (by
      show ((2 : O) : K) * 2⁻¹ = 1
      rw [show ((2 : O) : K) = 2 from rfl, mul_inv_cancel₀ h2])
    exact ⟨⟨2, ⟨_, h2i⟩, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  obtain ⟨XO, hXadm, hXdet⟩ := H cO hcOi h2O SO hSOdet hSOskew g.toBlocks₁₁ g.toBlocks₁₂ g.toBlocks₂₁ g.toBlocks₂₂
    (by rwa [fromBlocks_toBlocks]) (by rw [fromBlocks_toBlocks]; exact hunitO)

  obtain ⟨X, hX⟩ : ∃ X, XO.map O.subtype = X := ⟨_, rfl⟩
  have hXint : ∀ i j, X i j ∈ O := by rw [← hX]; intro i j; exact (XO i j).2
  have hadm : Xᵀ * ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c) + ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c) * X.map c = 0 := by
    have hK : Xᵀ * (δ • ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c)) + (δ • ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c)) * X.map c = 0 := by
      have := congrArg (fun Y => Y.map O.subtype) hXadm
      rwa [Matrix.map_add _ (map_add O.subtype), Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, mapc, hX, hSO,
        Matrix.map_zero _ (map_zero O.subtype)] at this
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd; ext i; exact i.elim0
    · have hδ0 : δ ≠ 0 := by
        haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
        rintro rfl; apply hdet; rw [zero_smul]; exact Matrix.det_zero
      rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_add] at hK
      exact (smul_eq_zero.mp hK).resolve_left hδ0
  have hUU : (fromBlocks 1 X 0 1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) K) * fromBlocks 1 (-X) 0 1 = 1 := by
    rw [fromBlocks_multiply]; simp
  have hUform : (fromBlocks 1 X 0 1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) K)ᵀ * ((wM b)ᵀ * dbl J * (wM b).map c) *
      (fromBlocks 1 X 0 1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) K).map c = (wM b)ᵀ * dbl J * (wM b).map c := by
    rw [hgram, fromBlocks_transpose, fromBlocks_map, Matrix.map_one _ (map_zero c) (map_one c),
      Matrix.map_zero _ (map_zero c), fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.transpose_one, Matrix.transpose_zero, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul,
      Matrix.mul_zero, add_zero, zero_add]
    congr 1
    have e : ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c + (b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c) * X.map c + Xᵀ * ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c + (b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c) =
        (Xᵀ * ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c) + ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c) * X.map c) +
          (Xᵀ * ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c) + ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c) * X.map c) := by
      simp only [Matrix.mul_add, Matrix.add_mul]; abel
    rw [e, hadm, add_zero]

  have hBBi : (b : Matrix (Fin d) (Fin d) K) * ((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := Units.mul_inv b
  have hBiB : ((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * (b : Matrix (Fin d) (Fin d) K) = 1 := Units.inv_mul b
  refine ⟨wM b * fromBlocks 1 X 0 1 * wMi b, wM b * fromBlocks 1 (-X) 0 1 * wMi b, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show wM b * fromBlocks 1 X 0 1 * wMi b * (wM b * fromBlocks 1 (-X) 0 1 * wMi b) =
        wM b * (fromBlocks 1 X 0 1 * (wMi b * wM b) * fromBlocks 1 (-X) 0 1) * wMi b by simp only [Matrix.mul_assoc],
      hWiW, Matrix.mul_one, hUU, Matrix.mul_one, hWW]
  · rw [conj_form', hUform, back_form c _ _ _ hWW]
  · have key : wM b * fromBlocks 1 X 0 1 * wMi b * @diagCols K _ (Fin d) _ = @diagCols K _ (Fin d) _ := by
      rw [show wM b * fromBlocks 1 X 0 1 * wMi b * @diagCols K _ (Fin d) _ =
          wM b * ((fromBlocks 1 X 0 1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) K) * (wMi b * @diagCols K _ (Fin d) _)) by
            simp only [Matrix.mul_assoc],
        wMi_diagCols b h2, fromBlocks_mul_fromRows_eq]
      simp only [Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
      rw [← wMi_diagCols b h2, ← Matrix.mul_assoc, hWW, Matrix.one_mul]
    exact key
  · have hc1 : ∀ Y : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) K, wMi b * (wM b * Y * wMi b) * wM b = Y := by
      intro Y; simp only [← Matrix.mul_assoc, hWiW, Matrix.one_mul]; rw [Matrix.mul_assoc, hWiW, Matrix.mul_one]
    intro z hz
    refine ⟨keeps_of_int O b h2i h2 _ ?_ z hz, keeps_of_int O b h2i h2 _ ?_ z hz⟩
    · rw [hc1]; exact intU O X hXint
    · rw [hc1]; exact intU O (-X) (fun i j => by rw [Matrix.neg_apply]; exact neg_mem (hXint i j))
  · have hPM : wMi b * (wM b * fromBlocks 1 X 0 1 * wMi b * M) * wM b = fromBlocks 1 X 0 1 * (wMi b * M * wM b) := by
      simp only [← Matrix.mul_assoc, hWiW, Matrix.one_mul]
    have hgb : g.map O.subtype = fromBlocks (g.toBlocks₁₁.map O.subtype) (g.toBlocks₁₂.map O.subtype)
        (g.toBlocks₂₁.map O.subtype) (g.toBlocks₂₂.map O.subtype) := by
      rw [← fromBlocks_map, fromBlocks_toBlocks]
    have hblk := toBlocks₁₁_conj b (wM b * fromBlocks 1 X 0 1 * wMi b * M)
    rw [hPM, ← hg, hgb, fromBlocks_multiply, toBlocks_fromBlocks₁₁] at hblk
    have hEK : (g.toBlocks₁₁ + XO * g.toBlocks₂₁).map O.subtype =
        1 * g.toBlocks₁₁.map O.subtype + X * g.toBlocks₂₁.map O.subtype := by
      rw [Matrix.map_add _ (map_add O.subtype), Matrix.map_mul, hX, Matrix.one_mul]
    have hE1 : (g.toBlocks₁₁ + XO * g.toBlocks₂₁)⁻¹ * (g.toBlocks₁₁ + XO * g.toBlocks₂₁) = 1 :=
      Matrix.nonsing_inv_mul _ hXdet
    have hEinv : ∀ Y : Matrix (Fin d) (Fin d) K, (g.toBlocks₁₁ + XO * g.toBlocks₂₁)⁻¹.map O.subtype *
        ((g.toBlocks₁₁ + XO * g.toBlocks₂₁).map O.subtype * Y) = Y := by
      intro Y
      rw [← Matrix.mul_assoc, ← Matrix.map_mul, hE1, Matrix.map_one _ (map_zero O.subtype) (map_one O.subtype),
        Matrix.one_mul]
    have e1 : ∀ Y : Matrix (Fin d) (Fin d) K, ((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * ((b : Matrix (Fin d) (Fin d) K) * Y) = Y := by
      intro Y; rw [← Matrix.mul_assoc, hBiB, Matrix.one_mul]
    refine ⟨(b : Matrix (Fin d) (Fin d) K) * (g.toBlocks₁₁ + XO * g.toBlocks₂₁)⁻¹.map O.subtype * ((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K), ?_, ?_⟩
    · have hQ : ∀ Q : Matrix (Fin d) (Fin d) K, Q = (b : Matrix (Fin d) (Fin d) K) * (((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * Q * (b : Matrix (Fin d) (Fin d) K)) * ((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
        intro Q; simp only [← Matrix.mul_assoc, hBBi, Matrix.one_mul]; rw [Matrix.mul_assoc, hBBi, Matrix.mul_one]
      rw [hQ ((2 : K)⁻¹ • _), ← hblk, ← hEK]
      simp only [Matrix.mul_assoc, e1, hEinv, hBBi]
    · intro u hu i
      show (((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ (((b : Matrix (Fin d) (Fin d) K) * (g.toBlocks₁₁ + XO * g.toBlocks₂₁)⁻¹.map O.subtype * ((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) *ᵥ u)) i ∈ O
      rw [Matrix.mulVec_mulVec, show ((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * ((b : Matrix (Fin d) (Fin d) K) * (g.toBlocks₁₁ + XO * g.toBlocks₂₁)⁻¹.map O.subtype * ((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) =
          (g.toBlocks₁₁ + XO * g.toBlocks₂₁)⁻¹.map O.subtype * ((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) by
        simp only [← Matrix.mul_assoc, hBiB, Matrix.one_mul], ← Matrix.mulVec_mulVec]
      exact intMulVec O _ _ (fun i j => ((g.toBlocks₁₁ + XO * g.toBlocks₂₁)⁻¹ i j).2) hu i
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceBigCellLocalUnitaryDecompositionStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_bigCell_local_unitary_decomposition : (∀ {O : Type} [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) O), IsUnit S.det → Sᵀ = -S.map c →
    ∀ (A B C D : Matrix (Fin n) (Fin n) O), IsUnit (Matrix.fromBlocks A B C D).det →
      (Matrix.fromBlocks A B C D)ᵀ * Matrix.fromBlocks 0 S S 0 * (Matrix.fromBlocks A B C D).map c =
        Matrix.fromBlocks 0 S S 0 →
      ∃ X : Matrix (Fin n) (Fin n) O, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det) →
  ∀ {K : Type} [Field K] (O : ValuationSubring K) (c : K →+* K), (∀ x, c (c x) = x) → (∀ x ∈ O, c x ∈ O) → (2 : K)⁻¹ ∈ O → (2 : K) ≠ 0 →
  ∀ {d : ℕ} (J : Matrix (Fin d) (Fin d) K), Jᵀ = -J.map c →
  ∀ (b : GL (Fin d) K) (δ : K), c δ = δ →
  (∀ i j, (δ • ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c)) i j ∈ O) →
  (δ • ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c)).det ≠ 0 →
  (δ • ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c)).det⁻¹ ∈ O →
  ∀ M M' : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) K, M * M' = 1 → Mᵀ * dbl J * M.map c = dbl J →
  (∀ z, GlobalTheory.InertBigCell.InLat2 O b z → GlobalTheory.InertBigCell.InLat2 O b (M *ᵥ z) ∧ GlobalTheory.InertBigCell.InLat2 O b (M' *ᵥ z)) →
  ∃ P P' : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) K, P * P' = 1 ∧ Pᵀ * dbl J * P.map c = dbl J ∧
    P * diagCols (Fin d) = diagCols (Fin d) ∧
    (∀ z, GlobalTheory.InertBigCell.InLat2 O b z → GlobalTheory.InertBigCell.InLat2 O b (P *ᵥ z) ∧ GlobalTheory.InertBigCell.InLat2 O b (P' *ᵥ z)) ∧
    ∃ N : Matrix (Fin d) (Fin d) K,
      N * ((2 : K)⁻¹ • ((P * M).toBlocks₁₁ + (P * M).toBlocks₁₂ + (P * M).toBlocks₂₁ + (P * M).toBlocks₂₂)) = 1 ∧
      ∀ u, GlobalTheory.InertBigCell.InLat O b u → GlobalTheory.InertBigCell.InLat O b (N *ᵥ u) := by
  first | exact @GlobalTheory.InertCellLocal.bigCell_local_step | exact GlobalTheory.InertCellLocal.bigCell_local_step | (intros; apply GlobalTheory.InertCellLocal.bigCell_local_step <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertCompletionConjugationProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertCompletionConjugationProperties
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.InertBigCell

theorem conjW_props : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
  B.IsGood σ → ∀ {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w),
  (∀ x, GlobalTheory.InertBigCell.conjW σ hw (GlobalTheory.InertBigCell.conjW σ hw x) = x) ∧
  (∀ x ∈ w.adicCompletionIntegers E, GlobalTheory.InertBigCell.conjW σ hw x ∈ w.adicCompletionIntegers E) ∧
  (2 : w.adicCompletion E)⁻¹ ∈ w.adicCompletionIntegers E ∧
  (∀ e : E, GlobalTheory.InertBigCell.conjW σ hw (algebraMap E (w.adicCompletion E) e) = algebraMap E (w.adicCompletion E) (σ e)) := by
  intro F E _ _ _ _ _ σ B hB v w hw
  have h := GlobalTheory.LFun.under_eq_of_isInertAt hw
  have hc : GlobalTheory.LFun.IsConjAt σ h (GlobalTheory.InertBigCell.conjW σ hw) := fun y =>
    congrArg (fun z => GlobalTheory.LFun.toCompl h (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ z))
      ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm_apply_apply y)
  obtain ⟨ϖ, hU⟩ := GlobalTheory.LFun.InertChart.exists_isUnramInv hB.cm hw hc
  obtain ⟨hcc, -⟩ := hU
  refine ⟨hcc, fun x hx => GlobalTheory.LFun.InertChart.conj_mem hw hc hx, ?_,
    fun e => GlobalTheory.LFun.InertChart.conj_algebraMap hc e⟩
  have h2 := GlobalTheory.LFun.complMap_mem h (GlobalTheory.InertLocField.half_mem v (hB.inert v w hw).1)
  rw [GlobalTheory.LFun.complMap_algebraMap] at h2
  rwa [map_inv₀, map_inv₀, map_ofNat, map_ofNat] at h2

end GlobalTheory.InertBigCell
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertCompletionConjugationPropertiesStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertCompletionConjugation_properties : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
  B.IsGood σ → ∀ {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w),
  (∀ x, GlobalTheory.InertBigCell.conjW σ hw (GlobalTheory.InertBigCell.conjW σ hw x) = x) ∧
  (∀ x ∈ w.adicCompletionIntegers E, GlobalTheory.InertBigCell.conjW σ hw x ∈ w.adicCompletionIntegers E) ∧
  (2 : w.adicCompletion E)⁻¹ ∈ w.adicCompletionIntegers E ∧
  (∀ e : E, GlobalTheory.InertBigCell.conjW σ hw (algebraMap E (w.adicCompletion E) e) = algebraMap E (w.adicCompletion E) (σ e)) := by
  first | exact @GlobalTheory.InertBigCell.conjW_props | exact GlobalTheory.InertBigCell.conjW_props | (intros; apply GlobalTheory.InertBigCell.conjW_props <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceBigCellStabiliserOfLocalRingBigCellLem
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertBigCell

theorem exists_bigCell : (∀ {O : Type} [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) O), IsUnit S.det → Sᵀ = -S.map c →
    ∀ (A B C D : Matrix (Fin n) (Fin n) O), IsUnit (Matrix.fromBlocks A B C D).det →
      (Matrix.fromBlocks A B C D)ᵀ * Matrix.fromBlocks 0 S S 0 * (Matrix.fromBlocks A B C D).map c =
        Matrix.fromBlocks 0 S S 0 →
      ∃ X : Matrix (Fin n) (Fin n) O, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det) →
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ g ∈ GlobalTheory.DblVac.KD σ W v,
      ∃ p ∈ GlobalTheory.DblVac.KD σ W v, p ∈ GlobalTheory.DblVac.PDiag σ W ∧ p * g ∈ GlobalTheory.DblVac.KD σ W v ∧ GlobalTheory.DblVac.BigCell W v (p * g) := by
  intro H F E _ _ _ _ _ σ B d W r s hB hW v w hw g hg
  obtain ⟨hinj, -, -, -, -, -, -⟩ := GlobalTheory.T.inertCompletionToAdeles_properties σ hw
  obtain ⟨gmul, gone, ginj, gat, gsurj, gvec⟩ := GlobalTheory.T.adelicMatrixGluedAtInertPlace_properties hw (ι := Fin d ⊕ Fin d)
  obtain ⟨gmul', gone', -, -, -, gvec'⟩ := GlobalTheory.T.adelicMatrixGluedAtInertPlace_properties hw (ι := Fin d)
  obtain ⟨hJ, -, -⟩ := GlobalTheory.T.adelicMatrix_trivial_off_inertPlace_unitary_at_place σ hw (ι := Fin d ⊕ Fin d)
  obtain ⟨-, hdiag, hhalfblk⟩ := GlobalTheory.T.adelicMatrix_trivial_off_inertPlace_unitary_at_place σ hw (ι := Fin d)
  obtain ⟨b, δ, hb, hδ, hint, hdet, hdetinv⟩ := GlobalTheory.T.exists_unimodular_frame_inertPlace σ B W r s hB hW hw
  obtain ⟨cc, cO, h2, calg⟩ := GlobalTheory.T.inertCompletionConjugation_properties σ B hB hw
  have hlat := GlobalTheory.T.mem_adelicLatticeAtFinitePlace_iff_inert hw W

  have hvec : ∀ x : Fin d → w.adicCompletion E,
      (fun i => iotaW hw (x i)) ∈ GlobalTheory.InertSph.latAt W v ↔ InLat (w.adicCompletionIntegers E) b x := by
    intro x
    rw [hlat]
    constructor
    · rintro ⟨u, hu, he⟩
      have hxu : x = u := funext fun i => hinj (congrFun he i)
      subst hxu
      exact (hb x).1 hu
    · intro hx
      exact ⟨x, (hb x).2 hx, rfl⟩
  have hvec2 : ∀ x : Fin d ⊕ Fin d → w.adicCompletion E,
      (fun i => iotaW hw (x i)) ∈ GlobalTheory.DblVac.latD W v ↔ InLat2 (w.adicCompletionIntegers E) b x := by
    intro x
    exact and_congr (hvec (x ∘ Sum.inl)) (hvec (x ∘ Sum.inr))
  have hsurj2 : ∀ z ∈ GlobalTheory.DblVac.latD W v, ∃ x : Fin d ⊕ Fin d → w.adicCompletion E,
      z = fun i => iotaW hw (x i) := by
    rintro z ⟨h1, h2⟩
    obtain ⟨x1, -, e1⟩ := (hlat _).1 h1
    obtain ⟨x2, -, e2⟩ := (hlat _).1 h2
    refine ⟨Sum.elim x1 x2, funext fun i => ?_⟩
    rcases i with i | i
    · exact congrFun e1 i
    · exact congrFun e2 i

  have hpres : ∀ P : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (w.adicCompletion E),
      (∀ x, InLat2 (w.adicCompletionIntegers E) b x → InLat2 (w.adicCompletionIntegers E) b (P *ᵥ x)) →
      ∀ z ∈ GlobalTheory.DblVac.latD W v, glueW hw P *ᵥ z ∈ GlobalTheory.DblVac.latD W v := by
    intro P hP z hz
    obtain ⟨x, rfl⟩ := hsurj2 z hz
    rw [gvec]
    exact (hvec2 _).2 (hP x ((hvec2 x).1 hz))
  have hpres' : ∀ P : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (w.adicCompletion E),
      (∀ z ∈ GlobalTheory.DblVac.latD W v, glueW hw P *ᵥ z ∈ GlobalTheory.DblVac.latD W v) →
      ∀ x, InLat2 (w.adicCompletionIntegers E) b x → InLat2 (w.adicCompletionIntegers E) b (P *ᵥ x) := by
    intro P hP x hx
    have := hP _ ((hvec2 x).2 hx)
    rw [gvec] at this
    exact (hvec2 _).1 this

  have e1 : incM F (dbl W.J) = dbl (incM F W.J) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [incM, dbl]
  have e2 : (dbl W.J).map (algebraMap E (w.adicCompletion E)) = dbl (W.J.map (algebraMap E (w.adicCompletion E))) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [dbl]
  have hskew : (W.J.map (algebraMap E (w.adicCompletion E)))ᵀ =
      -(W.J.map (algebraMap E (w.adicCompletion E))).map (conjW σ hw) := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.neg_apply, calg, hW.skew j i, map_neg, neg_neg]
  have h2ne : (2 : w.adicCompletion E) ≠ 0 := by
    have h := (algebraMap E (w.adicCompletion E)).injective.ne (two_ne_zero : (2 : E) ≠ 0)
    rw [show (2 : w.adicCompletion E) = algebraMap E (w.adicCompletion E) 2 from (map_ofNat _ 2).symm]
    exact h

  obtain ⟨hgat, hglat⟩ := hg
  have hgg : GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.matD g⁻¹ = 1 := Units.mul_inv g.1
  have hgg' : GlobalTheory.DblVac.matD g⁻¹ * GlobalTheory.DblVac.matD g = 1 := Units.inv_mul g.1
  have hginvat : At (evFin F v) (GlobalTheory.DblVac.matD g⁻¹ - 1) := by
    intro u hu
    have e : GlobalTheory.DblVac.matD g⁻¹ - 1 = -(GlobalTheory.DblVac.matD g⁻¹ * (GlobalTheory.DblVac.matD g - 1)) := by
      rw [Matrix.mul_sub, hgg', Matrix.mul_one, neg_sub]
    rw [e, smul_neg, ← Matrix.mul_smul, hgat u hu, Matrix.mul_zero, neg_zero]
  obtain ⟨P, hP⟩ := gsurj _ hgat
  obtain ⟨Q, hQ⟩ := gsurj _ hginvat
  have hPQ : P * Q = 1 := ginj (by rw [gmul, hP, hQ, gone]; exact hgg)
  have hU : Pᵀ * dbl (W.J.map (algebraMap E (w.adicCompletion E))) * P.map (conjW σ hw) =
      dbl (W.J.map (algebraMap E (w.adicCompletion E))) := by
    rw [← e2]
    apply (hJ (dbl W.J) P).1
    rw [hP, e1]
    exact g.2
  have hPlat : ∀ z, InLat2 (w.adicCompletionIntegers E) b z →
      InLat2 (w.adicCompletionIntegers E) b (P *ᵥ z) ∧ InLat2 (w.adicCompletionIntegers E) b (Q *ᵥ z) :=
    fun z hz => ⟨hpres' P (fun y hy => by rw [hP]; exact (hglat y hy).1) z hz,
      hpres' Q (fun y hy => by rw [hQ]; exact (hglat y hy).2) z hz⟩

  obtain ⟨P0, P0', hPP, hP0U, hP0d, hP0lat, N, hN, hNlat⟩ :=
    GlobalTheory.T.inertPlace_bigCell_local_unitary_decomposition H (w.adicCompletionIntegers E) (conjW σ hw) cc cO h2 h2ne
      (W.J.map (algebraMap E (w.adicCompletion E))) hskew b δ hδ hint hdet hdetinv P Q hPQ hU hPlat

  let u : GL (Fin d ⊕ Fin d) (AE F E) :=
    ⟨glueW hw P0, glueW hw P0', by rw [← gmul, hPP, gone], by
      have hPP' : P0' * P0 = 1 := mul_eq_one_comm.mp hPP
      rw [← gmul, hPP', gone]⟩
  have hu : u ∈ UG (cA σ) (dbl (incM F W.J)) := by
    show (glueW hw P0)ᵀ * dbl (incM F W.J) * (glueW hw P0).map (cA σ) = dbl (incM F W.J)
    rw [← e1]
    apply (hJ (dbl W.J) P0).2
    rw [e2]
    exact hP0U
  let p : GlobalTheory.DblVac.UD σ W := ⟨u, hu⟩
  have hp : GlobalTheory.DblVac.matD p = glueW hw P0 := rfl
  have hp' : GlobalTheory.DblVac.matD p⁻¹ = glueW hw P0' := rfl
  have hmul : ∀ a c : GlobalTheory.DblVac.UD σ W, GlobalTheory.DblVac.matD (a * c) = GlobalTheory.DblVac.matD a * GlobalTheory.DblVac.matD c :=
    fun _ _ => rfl
  have hpl : ∀ z ∈ GlobalTheory.DblVac.latD W v, GlobalTheory.DblVac.matD p *ᵥ z ∈ GlobalTheory.DblVac.latD W v :=
    hpres P0 (fun x hx => (hP0lat x hx).1)
  have hpl' : ∀ z ∈ GlobalTheory.DblVac.latD W v, GlobalTheory.DblVac.matD p⁻¹ *ᵥ z ∈ GlobalTheory.DblVac.latD W v :=
    hpres P0' (fun x hx => (hP0lat x hx).2)
  have hpg : GlobalTheory.DblVac.matD (p * g) = glueW hw (P0 * P) := by
    rw [gmul, hP]
    rfl
  refine ⟨p, ⟨?_, fun z hz => ⟨hpl z hz, hpl' z hz⟩⟩, ⟨1, ?_⟩, ⟨?_, fun z hz => ⟨?_, ?_⟩⟩, ?_⟩
  · rw [hp]
    exact gat P0
  · rw [hp]
    refine (hdiag P0 hP0d).trans ?_
    exact (Matrix.mul_one _).symm
  · rw [hpg]
    exact gat _
  · rw [hmul, ← Matrix.mulVec_mulVec]
    exact hpl _ (hglat z hz).1
  · rw [mul_inv_rev, hmul, ← Matrix.mulVec_mulVec]
    exact (hglat _ (hpl' z hz)).2
  ·
    refine ⟨glueW hw N, ?_, ?_⟩
    · have hd : GlobalTheory.DblVac.diagonalBlockOfMatrix (p * g) = glueW hw ((2 : w.adicCompletion E)⁻¹ •
          ((P0 * P).toBlocks₁₁ + (P0 * P).toBlocks₁₂ + (P0 * P).toBlocks₂₁ + (P0 * P).toBlocks₂₂)) := by
        unfold GlobalTheory.DblVac.diagonalBlockOfMatrix
        rw [hpg]
        exact hhalfblk _
      rw [hd, ← gmul', hN, gone']
    · intro z hz
      obtain ⟨x, hx, rfl⟩ := (hlat z).1 hz
      rw [gvec']
      exact (hvec _).2 (hNlat x ((hb x).1 hx))

end GlobalTheory.InertBigCell
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceBigCellStabiliserOfLocalRingBigCellLemStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_bigCell_stabiliser_of_localRingBigCell_lemma : (∀ {O : Type} [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) O), IsUnit S.det → Sᵀ = -S.map c →
    ∀ (A B C D : Matrix (Fin n) (Fin n) O), IsUnit (Matrix.fromBlocks A B C D).det →
      (Matrix.fromBlocks A B C D)ᵀ * Matrix.fromBlocks 0 S S 0 * (Matrix.fromBlocks A B C D).map c =
        Matrix.fromBlocks 0 S S 0 →
      ∃ X : Matrix (Fin n) (Fin n) O, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det) →
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ g ∈ GlobalTheory.DblVac.KD σ W v,
      ∃ p ∈ GlobalTheory.DblVac.KD σ W v, p ∈ GlobalTheory.DblVac.PDiag σ W ∧ p * g ∈ GlobalTheory.DblVac.KD σ W v ∧ GlobalTheory.DblVac.BigCell W v (p * g) := by
  first | exact @GlobalTheory.InertBigCell.exists_bigCell | exact GlobalTheory.InertBigCell.exists_bigCell | (intros; apply GlobalTheory.InertBigCell.exists_bigCell <;> assumption)
end
