module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehShapeIffOfDiscreteSpectrum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehDataUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieDerivativeRealLieSmoothingEqDensity
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointPicardClassEqTranslateOfTrivialLambda
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfFderivEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagMemDoubledVacuumLatticeStabilizer
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagMemDoubledVacuumLatticeStabilizer
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblVacDiag

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mat_mul_mat_inv {σ : E →ₐ[F] E} {d : ℕ} {J : Matrix (Fin d) (Fin d) E} (k : UA σ J) :
    mat k * mat k⁻¹ = 1 := by
  show ((k * k⁻¹ : UA σ J) : GL (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))).1 = 1
  rw [mul_inv_cancel]; rfl

theorem mat_inv_mul_mat {σ : E →ₐ[F] E} {d : ℕ} {J : Matrix (Fin d) (Fin d) E} (k : UA σ J) :
    mat k⁻¹ * mat k = 1 := by
  show ((k⁻¹ * k : UA σ J) : GL (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))).1 = 1
  rw [inv_mul_cancel]; rfl

def diagOne {R : Type} [CommRing R] {d : ℕ} (A B : Matrix (Fin d) (Fin d) R) (hAB : A * B = 1) (hBA : B * A = 1) :
    GL (Fin d ⊕ Fin d) R :=
  ⟨fromBlocks A 0 0 1, fromBlocks B 0 0 1, by simp [fromBlocks_multiply, hAB, ← fromBlocks_one],
    by simp [fromBlocks_multiply, hBA, ← fromBlocks_one]⟩

theorem diag_mem_KD (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) :
    ∀ k ∈ GlobalTheory.InertSph.KAt σ W v, ∃ g : GlobalTheory.DblVac.UD σ W,
      ((g : GL (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
        Matrix.fromBlocks (mat k) 0 0 1 ∧ g ∈ GlobalTheory.DblVac.KD σ W v := by
  intro k hk
  let M := diagOne (mat k) (mat k⁻¹) (mat_mul_mat_inv k) (mat_inv_mul_mat k)
  have hU : (M : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))ᵀ * dbl (incM F W.J) *
      (M : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))).map (cA σ) = dbl (incM F W.J) := by
    have hk2 : (mat k)ᵀ * incM F W.J * (mat k).map (cA σ) = incM F W.J := k.2
    show (fromBlocks (mat k) 0 0 1)ᵀ * fromBlocks (incM F W.J) 0 0 (-incM F W.J) *
      (fromBlocks (mat k) 0 0 (1 : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))).map (cA σ) = fromBlocks (incM F W.J) 0 0 (-incM F W.J)
    rw [fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, fromBlocks_multiply]
    simp [hk2, Matrix.map_one _ (map_zero (cA σ)) (map_one (cA σ))]
  refine ⟨⟨M, hU⟩, rfl, ?_, ?_⟩
  · intro u hu
    have h1 := hk.1 u hu
    show u • (fromBlocks (mat k) 0 0 1 - 1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = 0
    have h1' : u • (mat k - 1) = 0 := h1
    rw [← fromBlocks_one, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add, fromBlocks_smul, ← sub_eq_add_neg]
    simp [h1']
  · intro z hz
    have hinv : GlobalTheory.DblVac.matD (⟨M, hU⟩ : GlobalTheory.DblVac.UD σ W)⁻¹ = fromBlocks (mat k⁻¹) 0 0 1 := rfl
    have hfw : GlobalTheory.DblVac.matD (⟨M, hU⟩ : GlobalTheory.DblVac.UD σ W) = fromBlocks (mat k) 0 0 1 := rfl
    rw [hinv, hfw]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [fromBlocks_mulVec]; simpa using ((hk.2 _ hz.1).1)
    · rw [fromBlocks_mulVec]; simpa using hz.2
    · rw [fromBlocks_mulVec]; simpa using ((hk.2 _ hz.1).2)
    · rw [fromBlocks_mulVec]; simpa using hz.2

end GlobalTheory.DblVacDiag
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagMemDoubledVacuumLatticeStabilizerStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_diag_mem_doubledVacuumLatticeStabilizer : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d)
    (v : Pl (F := F)), ∀ k ∈ GlobalTheory.InertSph.KAt σ W v, ∃ g : GlobalTheory.DblVac.UD σ W,
      ((g : GL (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = Matrix.fromBlocks (mat k) 0 0 1 ∧
      g ∈ GlobalTheory.DblVac.KD σ W v := by
  first | exact @GlobalTheory.DblVacDiag.diag_mem_KD | exact GlobalTheory.DblVacDiag.diag_mem_KD | (intros; apply GlobalTheory.DblVacDiag.diag_mem_KD <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledSiegelParabolicDiagonalActionIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledSiegelParabolicDiagonalActionIntegral
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.InertDbl

theorem diag_mulVec_mem_latAt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) (M : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (h : M * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * t)
    (hM : ∀ z ∈ latAtD W v, M *ᵥ z ∈ latAtD W v) (z : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (hz : z ∈ GlobalTheory.InertSph.latAt W v) :
    t *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
  have key : ∀ y : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E),
      (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) *ᵥ y = Sum.elim y y := by
    intro y
    simp [diagCols, Matrix.fromRows_mulVec]
  have h1 : (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) *ᵥ z ∈ latAtD W v := by
    rw [key]; exact ⟨hz, hz⟩
  have h2 := hM _ h1
  rw [Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec, key] at h2
  exact h2.1

theorem parD_diag_action :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl (F := F)),
    ∀ p ∈ GlobalTheory.InertDbl.ParD σ W v, ∀ t : GL (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      GlobalTheory.InertDbl.matD p * diagCols (Fin d) = diagCols (Fin d) * (t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) →
      At (evFin F v) ((t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt W v, (t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v ∧
        ((t⁻¹ : GL (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
  intro F E _ _ _ _ _ σ d W v p hp t h'
  have h : matD p * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
      (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * (t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := h'
  obtain ⟨⟨hAt, hK⟩, -⟩ := hp
  have hinv : matD p⁻¹ * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
      (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * ((t⁻¹ : GL (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := by
    have h1 : matD p⁻¹ * matD p = 1 := p.1.inv_mul
    have h2 : (t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) *
        ((t⁻¹ : GL (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = 1 := t.mul_inv
    calc matD p⁻¹ * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
        = matD p⁻¹ * ((diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * ((t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) *
            ((t⁻¹ : GL (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))))) := by rw [h2, Matrix.mul_one]
      _ = _ := by
        rw [← Matrix.mul_assoc (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), ← h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  refine ⟨?_, fun z hz => ⟨diag_mulVec_mem_latAt W v _ _ h (fun y hy => (hK y hy).1) z hz,
    diag_mulVec_mem_latAt W v _ _ hinv (fun y hy => (hK y hy).2) z hz⟩⟩
  intro u hu
  have h0 := hAt u hu
  have h3 : (matD p - 1) * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * ((t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, h, Matrix.one_mul, Matrix.mul_one]
  have h4 : (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) *
      (u • ((t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1)) = 0 := by
    rw [Matrix.mul_smul, ← h3, ← Matrix.smul_mul, h0, Matrix.zero_mul]
  ext i j
  have h5 := congrFun (congrFun h4 (Sum.inl i)) j
  rw [diagCols, Matrix.fromRows_mul, Matrix.one_mul] at h5
  exact h5

end GlobalTheory.InertDbl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledSiegelParabolicDiagonalActionIntegralStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledSiegelParabolic_diagonal_action_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl (F := F)),
    ∀ p ∈ GlobalTheory.InertDbl.ParD σ W v, ∀ t : GL (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      GlobalTheory.InertDbl.matD p * diagCols (Fin d) = diagCols (Fin d) * (t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) →
      At (evFin F v) ((t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt W v, (t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v ∧
        ((t⁻¹ : GL (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
  first | exact @GlobalTheory.InertDbl.parD_diag_action | exact GlobalTheory.InertDbl.parD_diag_action | (intros; apply GlobalTheory.InertDbl.parD_diag_action <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbeddingPadicComplexInt
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectiveOfIsIntegral
namespace GlobalTheory.InjectiveOfIntegral

theorem exists_injective_of_isIntegral {A B O C : Type} [CommRing A] [IsDomain A] [CommRing B]
    [IsDomain B] [CommRing O] [Field C] [IsAlgClosed C] [Algebra O C] (v : Valuation C NNReal)
    (hv : Valuation.Integers v O) [Algebra A B] [Algebra.IsIntegral A B]
    (hAB : Function.Injective (algebraMap A B)) (j : A →+* O)
    (hj : Function.Injective ((algebraMap O C).comp j)) :
    ∃ j' : B →+* O, Function.Injective ((algebraMap O C).comp j') := by
  classical
  let _ : Algebra A C := ((algebraMap O C).comp j).toAlgebra
  let _ : Algebra A O := j.toAlgebra
  have : IsScalarTower A O C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hAC : Function.Injective (algebraMap A C) := hj
  have : Module.IsTorsionFree A B := Module.isTorsionFree_iff_algebraMap_injective.mpr hAB
  have : Module.IsTorsionFree A C := Module.isTorsionFree_iff_algebraMap_injective.mpr hAC
  have : Algebra.IsAlgebraic A B := Algebra.IsIntegral.isAlgebraic
  let ψ : B →ₐ[A] C := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hker : RingHom.ker (ψ : B →+* C) = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := A)
    ext a
    rw [Ideal.mem_comap, RingHom.mem_ker, Ideal.mem_bot,
      show (ψ : B →+* C) (algebraMap A B a) = algebraMap A C a from ψ.commutes a]
    exact ⟨fun h => hAC (h.trans (map_zero _).symm), fun h => by rw [h, map_zero]⟩
  have hψ : Function.Injective (ψ : B →+* C) := (RingHom.injective_iff_ker_eq_bot _).mpr hker
  have hint : ∀ b : B, v (ψ b) ≤ 1 := by
    intro b
    have hb : IsIntegral A (ψ b) := (Algebra.IsIntegral.isIntegral b).map ψ
    exact hv.mem_of_integral hb.tower_top
  choose g hg using fun b => hv.exists_of_le_one (hint b)
  let j' : B →+* O :=
    { toFun := g
      map_one' := hv.hom_inj (by simp only [hg, map_one])
      map_mul' := fun x y => hv.hom_inj (by simp only [hg, map_mul])
      map_zero' := hv.hom_inj (by simp only [hg, map_zero])
      map_add' := fun x y => hv.hom_inj (by simp only [hg, map_add (f := _)]) }
  refine ⟨j', ?_⟩
  have e : (algebraMap O C).comp j' = (ψ : B →+* C) := RingHom.ext hg
  rw [e]
  exact hψ

end GlobalTheory.InjectiveOfIntegral
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompleteDvrEmbedding

theorem exists_injective_of_integral {A B O C : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [CommRing O] [Field C] [IsAlgClosed C] [Algebra O C] (v : Valuation C NNReal) (hv : v.Integers O)
    [Algebra A B] [Algebra.IsIntegral A B] (hφ : Function.Injective (algebraMap A B)) (j : A →+* O)
    (hj : Function.Injective ((algebraMap O C).comp j)) :
    ∃ j' : B →+* O, Function.Injective ((algebraMap O C).comp j') := by
  first
  | (rename_i h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 h_14 h_15; revert A B O C h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 v hv h_14 h_15 hφ j hj; exact @_root_.GlobalTheory.InjectiveOfIntegral.exists_injective_of_isIntegral)
  | exact @_root_.GlobalTheory.InjectiveOfIntegral.exists_injective_of_isIntegral
  | exact _root_.GlobalTheory.InjectiveOfIntegral.exists_injective_of_isIntegral
  | (apply _root_.GlobalTheory.InjectiveOfIntegral.exists_injective_of_isIntegral <;> assumption)
  | (intros; apply _root_.GlobalTheory.InjectiveOfIntegral.exists_injective_of_isIntegral <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InjectiveOfIntegral.exists_injective_of_isIntegral <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InjectiveOfIntegral.exists_injective_of_isIntegral ..)

theorem exists_embedding_padicComplexInt :
    ∀ T : CDVR, T.FinRes → ∃ (p : ℕ) (_ : Fact p.Prime) (k : T.Fr →+* ℂ_[p]) (kO : T.V →+* 𝓞_ℂ_[p]), ∀ a, algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO a) = k (algebraMap T.V T.Fr a) := by
  intro T hT
  haveI : Finite (IsLocalRing.ResidueField T.V) := hT
  obtain ⟨p, hp, _, hfin⟩ := GlobalTheory.exists_padicInt_algebra_finite T.V
  have hinj : Function.Injective (algebraMap ℤ_[p] T.V) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra h0
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0
      (PadicInt.irreducible_p (p := p))
    rw [map_mul, map_pow, map_natCast] at ha
    exact mul_ne_zero (u.isUnit.map _).ne_zero
      (pow_ne_zero n (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) ha
  have hj : Function.Injective ((algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp (padicIntHom p)) :=
    (algebraMap ℚ_[p] ℂ_[p]).injective.comp Subtype.val_injective
  obtain ⟨kO, hkO⟩ := exists_injective_of_integral _ (PadicComplexInt.integers p) hinj (padicIntHom p) hj
  exact ⟨p, hp, IsFractionRing.lift (K := T.Fr) hkO, kO, fun a => (IsFractionRing.lift_algebraMap hkO a).symm⟩

end GlobalTheory.CompleteDvrEmbedding
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSphericalOfIsCompAlongSplit
open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SphBC

open GlobalTheory.PRep GlobalTheory.DefU

theorem isSpherical_of_isCompAlong_split {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
    {π : Submodule ℂ (UA E n → ℂ)} (hπ : IsAutRepU π) {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w)
    {X : Type} [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) X)
    (hc : IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) σ) (hu : IsUnramU π w) :
    GlobalTheory.LGrp.IsSpherical σ (GlobalTheory.LFun.KGL w (n := n)) := by
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E n w hw
  have hp : Function.Surjective ((cLoc w).comp (locU n w).subtype) := fun g =>
    ⟨e.symm g, (he _).symm.trans (e.apply_symm_apply g)⟩
  obtain ⟨φ, hφ, hφ0, hφK⟩ := hu
  by_contra hns
  have hfix : ∀ v, (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), σ k v = v) → v = 0 := by
    intro v hv
    by_contra hv0
    exact hns ((Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.LGrp.mem_fixed.2 hv, hv0⟩)
  obtain ⟨hσirr, f, hf0, hfm, hf⟩ := hc
  let Ψ : AutSub E n := ⟨π, hπ⟩
  have hirr : Representation.IsIrreducible (σ.comp ((cLoc w).comp (locU n w).subtype)) := by
    obtain ⟨h0, h1⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 hσirr
    refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun Y hY => h1 Y fun g v hv => ?_⟩
    obtain ⟨x, rfl⟩ := hp g
    exact hY x v hv
  let F : Representation.IntertwiningMap (σ.comp ((cLoc w).comp (locU n w).subtype)) (Ψ.rep.comp (locU n w).subtype) :=
    ⟨f.codRestrict _ hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf x v)⟩
  have hF0 : F ≠ 0 := fun h => hf0 (LinearMap.ext fun v => by
    have := congrArg Subtype.val (DFunLike.congr_fun h v)
    exact this)
  obtain ⟨r, -, -, hr⟩ := GlobalTheory.DefU.LocRet.exists_ret E n w
  have htop := (GlobalTheory.CuspRep.CompUniq.isotypic (UA E n) (locU n w) Ψ.V X X Ψ.rep (locU n w).subtype
    (σ.comp ((cLoc w).comp (locU n w).subtype)) (σ.comp ((cLoc w).comp (locU n w).subtype))
    Ψ.isIrreducible_rep hirr hirr (fun g => ⟨r g, fun y => hr g y⟩) F hF0).1
  let fi : Representation.IntertwiningMap (σ.comp ((cLoc w).comp (locU n w).subtype))
      (Ψ.rep.comp (locU n w).subtype) → X →ₗ[ℂ] (UA E n → ℂ) := fun i => π.subtype ∘ₗ i.toLinearMap
  have hfi : ∀ i g u, fi i ((σ.comp ((cLoc w).comp (locU n w).subtype)) g u) =
      (RU E n).comp (locU n w).subtype g (fi i u) := fun i g u =>
    congrArg Subtype.val (Representation.IntertwiningMap.isIntertwining _ _ i g u)
  have hmem : φ ∈ ⨆ i, LinearMap.range (fi i) := by
    have : φ ∈ (⨆ i : Representation.IntertwiningMap (σ.comp ((cLoc w).comp (locU n w).subtype))
        (Ψ.rep.comp (locU n w).subtype), LinearMap.range i.toLinearMap).map π.subtype := by
      rw [htop]; exact ⟨⟨φ, hφ⟩, Submodule.mem_top, rfl⟩
    simp only [fi, LinearMap.range_comp]
    rwa [Submodule.map_iSup] at this
  have key := GlobalTheory.InertHeckeEigen.mem_of_mem_iSup ((RU E n).comp (locU n w).subtype)
    (σ.comp ((cLoc w).comp (locU n w).subtype)) hirr fi hfi
    (((GlobalTheory.LFun.KGL w (n := n)).comap ((cLoc w).comp (locU n w).subtype) : Subgroup (locU n w)) : Set (locU n w)) ⊥
    (fun i v hv => by
      have hv' : v = 0 := hfix v fun k hk => by
        obtain ⟨x, rfl⟩ := hp k
        exact hv x hk
      rw [hv', map_zero]
      exact Submodule.zero_mem _)
    (fun z hz _ _ => by rw [(Submodule.mem_bot ℂ).1 hz, map_zero]) φ (fun k hk => hφK k.1 k.2 hk) hmem
  exact hφ0 ((Submodule.mem_bot ℂ).1 key)

theorem isSpherical_of_isUnramU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π →
    ∀ (c : ℕ) (a d : Fin c → ℕ) (h : ∑ i, d i * a i = n) (P : ∀ i, CuspSub E (a i))
      (ρ : ∀ i (w : HeightOneSpectrum (𝓞 E)), LocIrr w (a i)) (m : Fin c → (E →+* ℂ) → Multiset ℂ)
      (σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), LocIrr w (d i * a i)),
      GlobalTheory.BcSpeh.Parts π a d h P ρ m →
      (∀ i w, IsUnitarisable (ρ i w).ρ ∧ IsUnitarisable (σ i w).ρ ∧
        GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of (ρ i w).ρ (ρ i w).smooth (ρ i w).irred) (d i) (σ i w).ρ) →
      (∀ w, IsSplitAt w → IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) (locProd h w (σ · w))) →
      ∀ w, IsUnramU π w → ∀ i (τ : SmIrr (GL (Fin (a i)) (w.adicCompletion E))), (P i).IsLocComp w τ →
        GlobalTheory.LGrp.IsSpherical τ.ρ (GlobalTheory.LFun.KGL w (n := (a i))) := by
  intro E _ _ _ hE n π hπ c a d h P ρ m σ hp hsh hsplit w hu i τ hτ
  suffices hB : ∃ B, GlobalTheory.LFun.HasSatGL w (ρ i w).ρ B by
    obtain ⟨B, hB⟩ := hB
    have h1 := (GlobalTheory.BcSpehCompare.hasSat_iff (hp.loc i w) B).2 hB
    exact ((GlobalTheory.BcSpehCompare.hasSat_iff hτ B).1 h1).1
  by_cases hw : IsSplitAt w
  · have hc := hsplit w hw
    have hs : GlobalTheory.LGrp.IsSpherical (locProd h w (σ · w)) (GlobalTheory.LFun.KGL w (n := n)) :=
      isSpherical_of_isCompAlong_split hπ hw _ hc hu
    have hsm : GlobalTheory.PRep.IsSmooth (locProd h w (σ · w)) := GlobalTheory.SmGL.isSmooth_parInd _ _
    have hirr : (locProd h w (σ · w)).IsIrreducible := hc.1
    obtain ⟨T, hT⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible hsm hirr hs
    obtain ⟨S, hS, -⟩ := GlobalTheory.SatInd.satake_locProd_speh E w c n a d h (ρ · w) (σ · w) (fun i => (hp.pos i).2)
      (fun i => (hsh i w).2.2) T hT
    exact ⟨S i, hS i⟩
  · obtain ⟨s, ϖ, q, α, h1, h2, h3⟩ := GlobalTheory.BcSpehCompare.exists_hasSatAt hE hπ hw hu
    obtain ⟨S, hS, -⟩ := hp.inert w s ϖ q h1 h2 α h3
    exact ⟨S i, hS i⟩

end GlobalTheory.SphBC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDescendsFromGenericFibre
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
open scoped CategoryTheory.Obj

namespace GlobalTheory.ThetaExtend

theorem isRegularRing_sections {Y : Scheme.{0}} [IsLocallyNoetherian Y]
    (hY : ∀ y, IsRegularLocalRing (Y.presheaf.stalk y)) {V : Y.Opens} (hV : IsAffineOpen V) :
    IsRegularRing Γ(Y, V) := by
  have : IsNoetherianRing Γ(Y, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  rw [isRegularRing_iff]
  intro q hq
  let y : PrimeSpectrum Γ(Y, V) := ⟨q, hq⟩
  have hy : hV.fromSpec y ∈ V := hV.range_fromSpec.le ⟨y, rfl⟩
  let : Algebra Γ(Y, V) (Y.presheaf.stalk (hV.fromSpec y)) :=
    Y.presheaf.algebra_section_stalk ⟨hV.fromSpec y, hy⟩
  have h : IsLocalization q.primeCompl (Y.presheaf.stalk (hV.fromSpec y)) :=
    hV.isLocalization_stalk' y hy
  have := hY (hV.fromSpec y)
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv q.primeCompl (Y.presheaf.stalk (hV.fromSpec y))
      (Localization.AtPrime q)).toRingEquiv

theorem isRegularRing_stalk {X Y : Scheme.{0}} [IsLocallyNoetherian Y]
    (hY : ∀ y, IsRegularLocalRing (Y.presheaf.stalk y)) (f : X ⟶ Y) [Smooth f] (x : X) :
    IsRegularRing (X.presheaf.stalk x) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ f ⁻¹ᵁ V from hxV) (f ⁻¹ᵁ V).isOpen
  have hs : (f.appLE V U hUV).hom.Smooth :=
    HasRingHomProperty.appLE @Smooth f inferInstance ⟨V, hV⟩ ⟨U, hU⟩ hUV
  have := isRegularRing_sections hY hV
  algebraize [(f.appLE V U hUV).hom]
  have : IsRegularRing Γ(X, U) := isRegularRing_of_smooth Γ(Y, V) Γ(X, U)
  let := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  exact ExtendRig.isRegularRing_of_isLocalization (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl _

theorem ufd_of_regular (R : Type) [CommRing R] [IsRegularRing R] [IsLocalRing R] [IsDomain R] :
    UniqueFactorizationMonoid R :=
  uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing
    exists_hasProjectiveDimensionLE_of_isRegularLocalRing
    isPrincipal_map_away_of_hasProjectiveDimensionLE R

end GlobalTheory.ThetaExtend
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalLetterRealExponentEqZeroIffIsUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalLetterRealExponentEqZeroIffIsUnitary
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ResW

theorem rexp_eq_zero_iff_isUnitary : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (x : Letter E), 1 ≤ x.1 → (rexp x = 0 ↔ x.2.IsUnitary) ∧ (x.2.IsUnitary ↔ (CG.mk x.2).IsUnitary) := by
  intro E _ _ _ x ha
  refine ⟨?_, (CG.isUnitary_mk _).symm⟩
  have hc : ∀ φ ∈ x.2.V, zc E x.1 φ = cex x • φ :=
    Classical.epsilon_spec (p := fun c : ℂ => ∀ φ ∈ x.2.V, zc E x.1 φ = c • φ)
      (by rw [zc_eq_scL]; exact Central.lie_scalar x.2 (1 : Cinf E))
  have hd : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hpos : (0 : ℝ) < x.1 * Module.finrank ℚ E := by positivity
  have hz := (zc_comm_mem_eigen E x.1).2.2
  rw [rexp, div_eq_zero_iff, or_iff_left hpos.ne']
  constructor
  · intro h0
    have hne : (x.1 * (Module.finrank ℚ E : ℂ)) ≠ 0 := by exact_mod_cast hpos.ne'
    obtain ⟨χ, h1, -, h2, -⟩ := exists_abs_cpow E (-cex x / (x.1 * (Module.finrank ℚ E : ℂ)))
    have hre : (-cex x / (x.1 * (Module.finrank ℚ E : ℂ))).re = 0 := by
      rw [← Nat.cast_mul, Complex.div_natCast_re, Complex.neg_re, h0]; simp
    have hχ : χ.IsUnitary := fun y => by
      rw [h2, hre, nu, Model.eq_one_of_isAbsPow (GlobalTheory.HeckeGal.Model.absPow_isAbsPow E 0)]
      exact isUnitary_one y
    have hn : IsNormalised (x.2.twist χ) := by
      rintro _ ⟨φ, hφ, rfl⟩ t g
      have h3 : zc E x.1 (mulChi x.1 χ φ) = (0 : ℂ) • mulChi x.1 χ φ := by
        rw [h1, hc φ hφ, mul_div_cancel₀ _ hne, ← add_smul, add_neg_cancel, map_smul]
      simpa using (hz _ 0).1 h3 t g
    obtain ⟨ω, hω⟩ := Central.exists_hasCentral E x.1 x.2
    have h4 := ((hω.twist χ).isUnitary_iff.1 (GlobalTheory.SpehPair.isUnitary_of_isNormalised hn)).mul
      (isUnitary_pow hχ x.1).inv
    rw [mul_inv_cancel_right] at h4
    exact hω.isUnitary_iff.2 h4
  · intro hu
    obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 x.2.ne_bot
    obtain ⟨g, hg⟩ : ∃ g, φ.1 g ≠ 0 := Function.ne_iff.1 fun e => h0 (Subtype.ext e)
    have h1 := congrArg norm ((hz φ _).1 (hc φ hφ) 1 g)
    rw [splitCentre_eq_scalar, hu.norm_eq hφ, norm_mul, Complex.norm_exp] at h1
    have h2 := (mul_eq_right₀ (norm_ne_zero_iff.2 hg)).1 h1.symm
    simpa using h2

end GlobalTheory.ResW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalLetterRealExponentEqZeroIffIsUnitaryStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidalLetterRealExponent_eq_zero_iff_isUnitary : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (x : Letter E), 1 ≤ x.1 → (rexp x = 0 ↔ x.2.IsUnitary) ∧ (x.2.IsUnitary ↔ (CG.mk x.2).IsUnitary) := by
  first | exact @GlobalTheory.ResW.rexp_eq_zero_iff_isUnitary | exact GlobalTheory.ResW.rexp_eq_zero_iff_isUnitary | (intros; apply GlobalTheory.ResW.rexp_eq_zero_iff_isUnitary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelLiftModuliLawsOfCore
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelLiftModuliLawsOfCore
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory.LevCore

open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem dict_transport {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}
    {X : Comp → Data E r} {V W : HSp D} (h : V = W) (dict : GA D V → Σ k, Frame (X k).Ψ r)
    (d : GA D W → Σ k, Frame (X k).Ψ r) (hdd : ∀ g (h' : V = W), d g = dict (h' ▸ g))
    (Kf : Subgroup (GA D V)) (th : ∀ k, (X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hr : V.rank = r)
    (N : ℕ) (hl : IsLevelK V N Kf) (hd : DictIsUnif V dict Kf th hr)
    (hu : ∀ g τ i, ‖dmin (X (dict g).1).Gm (dict g).2 τ i‖ = 1) :
    ∃ (Kf' : Subgroup (GA D W)) (hr' : W.rank = r), IsLevelK W N Kf' ∧ DictIsUnif W d Kf' th hr' ∧
      ∀ g τ i, ‖dmin (X (d g).1).Gm (d g).2 τ i‖ = 1 := by
  subst h
  obtain rfl : d = dict := funext fun g => hdd g rfl
  exact ⟨Kf, hr, hl, hd, hu⟩

end GlobalTheory.LevCore


open GlobalTheory.LevCore in
theorem GlobalTheory.LevGeo.laws_of_coreJ : ∀ (D : D7) (T : CoreJ D) (j : ℕ), LawsJ T → InR D j → Laws D j (T.Q.Xo j) T.Q.c (T.U j) (coreDict T.toCore j) ∧ ∀ (G : WTZ D.host.E) (σ : T.Q.c.F →+* ℂ) (f : cuspW (T.Q.Xo j) T.Q.c (T.U j) G), normW (T.U j) (xiR D) (fun _ => D.sp.W j) (coreDict T.toCore j) G σ f = normW (T.U j) (xiR D) (T.V j) (T.dict j) G σ f := by
  intro D T j hT hj
  obtain ⟨hH, hL, _, hDat⟩ := hT.pins
  refine ⟨⟨hj, hH, hDat j hj, hL.2, hT.unf j hj, hT.chiTriv j hj, ?_, ?_⟩, ?_⟩
  · intro σ hσ
    obtain ⟨th, hr, hinf, hdu⟩ := hT.dictU j hj σ hσ
    obtain ⟨Kf', hr', h1, h2, h3⟩ := dict_transport (hT.spaceW j hj σ hσ) (T.dict j σ) (coreDict T.toCore j σ)
      (fun g h' => by unfold coreDict; rw [dite_eq_left h']) (T.Kf j σ) th hr _
      (hL.1 ▸ hT.levelK j hj σ hσ) hdu (hT.muUnit j hj σ hσ).2.2.2
    exact ⟨Kf', th, hr', h1, hinf, h2, h3⟩
  · intro σ hσ
    have h := hT.modelW j hj σ hσ
    rw [hT.spaceW j hj σ hσ] at h
    exact h
  · intro G σ f
    have hg := Formalism.L2.Pj.goodEmb_goodOf (c := T.Q.c) σ
    have key : ∀ (W : HSp D) (h : T.V j (Formalism.L2.Pj.goodOf T.Q.c σ) = W)
        (d : GA D W → Σ k, Frame ((T.U j (Formalism.L2.Pj.goodOf T.Q.c σ)).X k).Ψ D.R.r),
        (∀ g (h' : T.V j (Formalism.L2.Pj.goodOf T.Q.c σ) = W), d g = T.dict j _ (h' ▸ g)) →
        petAt (T.U j (Formalism.L2.Pj.goodOf T.Q.c σ)) (xiR D) W d (muQ1 W) G f =
          petAt (T.U j (Formalism.L2.Pj.goodOf T.Q.c σ)) (xiR D) (T.V j _) (T.dict j _) (muQ1 _) G f := by
      intro W h
      subst h
      intro d hdd
      obtain rfl : d = _ := funext fun g => hdd g rfl
      rfl
    exact key _ (hT.spaceW j hj _ hg) _ (fun g h' => by unfold coreDict; rw [dite_eq_left h'])
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelLiftModuliLawsOfCoreStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalLevelLiftModuliLaws_of_core : ∀ (D : D7) (T : CoreJ D) (j : ℕ), LawsJ T → InR D j → Laws D j (T.Q.Xo j) T.Q.c (T.U j) (coreDict T.toCore j) ∧ ∀ (G : WTZ D.host.E) (σ : T.Q.c.F →+* ℂ) (f : cuspW (T.Q.Xo j) T.Q.c (T.U j) G), normW (T.U j) (xiR D) (fun _ => D.sp.W j) (coreDict T.toCore j) G σ f = normW (T.U j) (xiR D) (T.V j) (T.dict j) G σ f := by
  first | exact @GlobalTheory.LevGeo.laws_of_coreJ | exact GlobalTheory.LevGeo.laws_of_coreJ | (intros; apply GlobalTheory.LevGeo.laws_of_coreJ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymTranslate
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricRigidTranslateLineBundleOfSquareDefect
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricRigidTranslateLineBundleOfSquareDefect
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open MonoidalCategory CartesianMonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic (Pic cls lam)

noncomputable section

namespace GlobalTheory.SymTranslate

theorem sym_rigTransl_of_sq : ∀ (K : Type) [Field K] (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B] (L : LB B.left) (hL : L.IsLB), (∃ t : LB.Gen (Theta B L), t.IsGen) → ∀ a : 𝟙_ (Over (Sp K)) ⟶ B, CechPic.pull (GrpObj.inv : B ⟶ B).left (cls L hL) - cls L hL = lam (cls L hL) (toUnit B ≫ a ^ 2) (𝟙 B) → Out.Sym B (GlobalTheory.RigidTranslate.rigTransl L a) := by
  intro K _ B _ _ L hL _ a h
  have hc : ∀ x : 𝟙_ (Over (Sp K)) ⟶ B, CechPic.pull (toUnit B ≫ x).left (cls L hL) = 0 := fun x => by
    rw [Over.comp_left, CechPic.pull_comp,
      GlobalTheory.PrimitiveOverField.pic_field (CechPic.pull x.left (cls L hL))]
    exact map_zero _
  have h1 : CechPic.pull (1 : B ⟶ B).left (cls L hL) = 0 := hc _
  have h2 : CechPic.pull (GrpObj.inv : B ⟶ B).left (cls L hL) =
      CechPic.pull ((toUnit B ≫ a ^ 2) * 𝟙 B).left (cls L hL) := by
    rw [lam, hc, h1, Over.id_left, CechPic.pull_id, sub_zero, add_zero] at h
    exact sub_left_injective h
  have h3 := congrArg (CechPic.pull (𝟙 B * (toUnit B ≫ a)⁻¹).left) h2
  rw [← CechPic.pull_comp, ← CechPic.pull_comp, ← Over.comp_left, ← Over.comp_left] at h3
  have e1 : (𝟙 B * (toUnit B ≫ a)⁻¹) ≫ (GrpObj.inv : B ⟶ B) =
      (GrpObj.inv : B ⟶ B) ≫ (𝟙 B * (toUnit B ≫ a)) := by
    rw [← Hom.inv_def, MonObj.comp_mul, ← Category.assoc, comp_toUnit, Category.comp_id, mul_inv, inv_inv,
      Hom.inv_def, Category.id_comp]
  have e2 : (𝟙 B * (toUnit B ≫ a)⁻¹) ≫ ((toUnit B ≫ a ^ 2) * 𝟙 B) = 𝟙 B * (toUnit B ≫ a) := by
    rw [MonObj.comp_mul, ← Category.assoc, comp_toUnit, Category.comp_id, MonObj.comp_pow, sq,
      _root_.mul_comm (𝟙 B), _root_.mul_comm (𝟙 B), _root_.mul_assoc, mul_inv_cancel_left]
  rw [e1, e2, Over.comp_left, CechPic.pull_comp] at h3
  have hL' : (GlobalTheory.RigidTranslate.rigTransl L a).IsLB := LB.isLB_linComb hL _ _
  have h4 : cls _ hL' = CechPic.pull (𝟙 B * (toUnit B ≫ a)).left (cls L hL) := by
    rw [CechPic.cls_linComb hL, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hc, smul_zero, add_zero, one_smul]
    rfl
  exact GlobalTheory.RigSymSubring.sym_of_cls hL' (by rw [h4]; exact h3)

end GlobalTheory.SymTranslate
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricRigidTranslateLineBundleOfSquareDefectStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open MonoidalCategory CartesianMonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic (Pic cls lam)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetric_rigidTranslateLineBundle_of_square_defect : ∀ (K : Type) [Field K] (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B] (L : LB B.left) (hL : L.IsLB), (∃ t : LB.Gen (Theta B L), t.IsGen) → ∀ a : 𝟙_ (Over (Sp K)) ⟶ B, CechPic.pull (GrpObj.inv : B ⟶ B).left (cls L hL) - cls L hL = lam (cls L hL) (toUnit B ≫ a ^ 2) (𝟙 B) → Out.Sym B (GlobalTheory.RigidTranslate.rigTransl L a) := by
  first | exact @GlobalTheory.SymTranslate.sym_rigTransl_of_sq | exact GlobalTheory.SymTranslate.sym_rigTransl_of_sq | (intros; apply GlobalTheory.SymTranslate.sym_rigTransl_of_sq <;> assumption)
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

open MonoidalCategory CartesianMonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic (Pic cls lam)
noncomputable section
namespace GlobalTheory.RiemannExists

theorem exists_sym_translate : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ (L : LB B.left) (hL : L.IsLB), Out.RelAmple B L → Out.KTriv B L → ∃ (L' : LB B.left) (hL' : L'.IsLB), Out.Rigidified B L' ∧ Out.Sym B L' ∧ Out.RelAmple B L' ∧ Out.KTriv B L' ∧ lam (cls L' hL') (fst B B) (snd B B) = lam (cls L hL) (fst B B) (snd B B) := by
  intro K _ _ B _ hB L hL ha hk
  have := hB.comm
  obtain ⟨c, hc⟩ := exists_gen_theta_of_isAbelianScheme K B hB L hL
  have hΘ : ∃ t : LB.Gen (Theta B L), t.IsGen := ⟨c, hc⟩
  obtain ⟨O, hO, eO⟩ := CechPic.cls_surj (CechPic.pull (GrpObj.inv : B ⟶ B).left (cls L hL) - cls L hL)
  have hlam : lam (cls O hO) (fst B B) (snd B B) = 0 := by
    rw [eO, PrimitiveOverField.lam_sub, CechPic.lam_pull, ← Hom.inv_def, ← Hom.inv_def,
      FormPoly.lam_inv_left hL hΘ, FormPoly.lam_inv_right hL hΘ, neg_neg, sub_self]
  obtain ⟨b, hb⟩ := GlobalTheory.T.exists_point_picardClass_eq_translate_of_trivial_lambda K B hB L hL hk O hO hlam
  obtain ⟨a, hab⟩ := SS.SemiDivisible.pow_surj_abelian K B hB (n := 2) (by norm_num) b
  have hL' : (RigidTranslate.rigTransl L a).IsLB := DVR.linComb_isLB _ hL _ _
  refine ⟨_, hL', RigidTranslate.rigidified_rigTransl hL, GlobalTheory.T.symmetric_rigidTranslateLineBundle_of_square_defect K B L hL hΘ a (by rw [← eO, hb, hab]),
    GlobalTheory.T.relAmple_rigidTranslateLineBundle_rationalPoint K B hB L hL a ha, GlobalTheory.T.kernelTrivial_rigidTranslateLineBundle _ B L hL a hk, ?_⟩
  have e := (CechPic.cls_eq_iff (LB.isLB_linComb hL' _ _) (pull_isLB (LB.isLB_linComb hL _ _) _)).2
    (RigidTranslate.lam_rigTransl (t := a) hL c hc)
  rw [CechPic.cls_pull (LB.isLB_linComb hL _ _), CechPic.pull_id] at e
  exact (CechPic.cls_cube_two hL' _ _ _).symm.trans (e.trans (CechPic.cls_cube_two hL _ _ _))

end GlobalTheory.RiemannExists
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormEqZeroOfLagrangianAtPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormEqZeroOfLagrangianAtPlace
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny

noncomputable section
namespace GlobalTheory.InertVacIso

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem smul_eq_map_compFin (v : Pl (F := F)) (a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    GlobalTheory.EmbChart.atPlace v 1 • a =
      TensorProduct.map (GlobalTheory.EmbChart.atPlace v) LinearMap.id (compFin F E v a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [smul_add, hx, hy, map_add (f := _), map_add (f := _)]
  | tmul x b =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, GlobalTheory.EmbChart.atPlace_mul_right, one_mul]
    simp [compFin, Algebra.TensorProduct.map_tmul]

theorem smul_eq_zero_of_compFin (v : Pl (F := F)) {a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)} (h : compFin F E v a = 0) :
    GlobalTheory.EmbChart.atPlace v 1 • a = 0 := by
  rw [smul_eq_map_compFin, h, map_zero]

theorem compFin_cA (σ : E →ₐ[F] E) (v : Pl (F := F)) (a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    compFin F E v (cA σ a) =
      Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ (compFin F E v a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]
  | tmul x b => simp [cA, compFin, Algebra.TensorProduct.map_tmul]

theorem self_eq_smul_of_at {n d : ℕ} (v : Pl (F := F)) {u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))} (h : At (evFin F v) u) :
    u = GlobalTheory.EmbChart.atPlace v 1 • u := by
  have h1 := h (1 - GlobalTheory.EmbChart.atPlace v 1) (by rw [map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at h1
  exact h1

theorem hTens_eq_sum {α β : Type} [Fintype α] [Fintype β] (c : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →ₐ[AF F] _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (x y : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    hTens c JA JB x y = ∑ i, ∑ k, JA i k * (x * JB * (y.map c)ᵀ) i k := by
  simp only [hTens, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem symp_eq_zero_of_lagAt : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n d m : ℕ}
    (JX : Matrix (Fin n) (Fin n) E) (W : Spc F E d) (v : Pl (F := F)) (C : Matrix (Fin d) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    GlobalTheory.InertVacLag.IsLagrAt σ W v C → ∀ (ξ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (u u' : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    u ∈ GlobalTheory.InertVacLag.lagAt v C → u' ∈ GlobalTheory.InertVacLag.lagAt v C →
    symp (cA σ) ξ (incM F JX) (incM F W.J) u u' = 0 := by
  intro F E _ _ _ _ _ σ n d m JX W v C hL ξ u u' hu hu'
  obtain ⟨hat, z, rfl⟩ := hu
  obtain ⟨-, z', rfl⟩ := hu'
  set e := GlobalTheory.EmbChart.atPlace v (1 : Fv F v)
  set P := Cᵀ * incM F W.J * C.map (cA σ) with hP
  have hPv : P.map (compFin F E v) = 0 := by
    have h1 := hL.1
    rw [hP, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
    convert h1 using 2
    · congr 1
    · ext i j
      simp only [Matrix.map_apply]
      exact compFin_cA σ v (C i j)
  have heP : e • P = 0 := by
    ext p q
    rw [Matrix.smul_apply, Matrix.zero_apply]
    apply smul_eq_zero_of_compFin
    have := congrArg (fun M => M p q) hPv
    simpa using this
  have hM : z * Cᵀ * incM F W.J * ((z' * Cᵀ).map (cA σ))ᵀ = 0 := by
    rw [self_eq_smul_of_at v hat]
    have hmap : (z' * Cᵀ).map (cA σ) = z'.map (cA σ) * Cᵀ.map (cA σ) :=
      Matrix.map_mul (f := (cA σ).toRingHom)
    rw [hmap, Matrix.transpose_mul, Matrix.transpose_map, Matrix.transpose_transpose]
    rw [Matrix.smul_mul, Matrix.smul_mul]
    have : z * Cᵀ * incM F W.J * (C.map (cA σ) * (z'.map (cA σ))ᵀ) = z * P * (z'.map (cA σ))ᵀ := by
      rw [hP]; simp only [Matrix.mul_assoc]
    rw [this, ← Matrix.smul_mul, ← Matrix.mul_smul, heP, Matrix.mul_zero, Matrix.zero_mul]
  rw [symp, hTens_eq_sum, hM]
  simp

end GlobalTheory.InertVacIso
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormEqZeroOfLagrangianAtPlaceStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplecticForm_eq_zero_of_lagrangianAtPlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n d m : ℕ}
    (JX : Matrix (Fin n) (Fin n) E) (W : Spc F E d) (v : Pl (F := F)) (C : Matrix (Fin d) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    GlobalTheory.InertVacLag.IsLagrAt σ W v C → ∀ (ξ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (u u' : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    u ∈ GlobalTheory.InertVacLag.lagAt v C → u' ∈ GlobalTheory.InertVacLag.lagAt v C →
    symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ξ ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JX) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) u u' = 0 := by
  first | exact @GlobalTheory.InertVacIso.symp_eq_zero_of_lagAt | exact GlobalTheory.InertVacIso.symp_eq_zero_of_lagAt | (intros; apply GlobalTheory.InertVacIso.symp_eq_zero_of_lagAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOne
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh GlobalTheory.CechPic

namespace GlobalTheory.NefCurveTest

theorem smoothOfRelativeDimension_one {k : Type} [Field k] {C : Scheme.{0}} [IsIntegral C] (s : C ⟶ Sp k) [Smooth s]
    (hd : topologicalKrullDim C = 1) : SmoothOfRelativeDimension 1 s := by
  obtain ⟨n, hn⟩ : ∃ n, SmoothOfRelativeDimension n s := exists_dim_of_preconnected s (genericPoint C)
  obtain ⟨x, hx⟩ := ProperCurve.exists_ne_genericPoint hd
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
  have e := (ProperCurve.ringKrullDim_eq_one hd hU hxU hx).symm.trans
    (SmoothDim.ringKrullDim_affineOpen k _ _ _ hn U hU ⟨x, hxU⟩)
  obtain rfl : 1 = n := by exact_mod_cast e
  exact hn

theorem exists_smooth_finite {k : Type} [Field k] [IsAlgClosed k] {D : Scheme.{0}} [IsIntegral D] (s : D ⟶ Sp k)
    [IsProper s] (hd : topologicalKrullDim D = 1) :
    ∃ (C : Scheme.{0}) (_ : IsIntegral C) (f : C ⟶ D), IsFinite f ∧ f (genericPoint C) = genericPoint D ∧
      topologicalKrullDim C = 1 ∧ Smooth (f ≫ s) := by
  let f := D.fromSpecResidueField (genericPoint D)
  let c := f.fromNormalization
  haveI : IsFinite c := NormCurve.isFinite_fromNormalization f s
  have htr : letI := (NormCurve.constHom (f ≫ s) ⊤).toAlgebra
      Algebra.trdeg k Γ(Spec (D.residueField (genericPoint D)), ⊤) ≤ 1 := by
    obtain ⟨x, hx⟩ := ProperCurve.exists_ne_genericPoint hd
    obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
    have e : ⊤ ≤ f ⁻¹ᵁ U := fun z _ => by
      change f z ∈ U
      rw [Scheme.fromSpecResidueField_apply]
      exact VB.genericPoint_mem hxU
    letI := (NormCurve.constHom s U).toAlgebra
    haveI : Algebra.FiniteType k Γ(D, U) := NormCurve.finiteType_constHom s hU
    haveI : Nonempty (⊤ : (Spec (D.residueField (genericPoint D))).Opens) :=
      ⟨⟨Nonempty.some inferInstance, trivial⟩⟩
    letI := (NormCurve.isField_sections (⊤ : (Spec (D.residueField (genericPoint D))).Opens)).toField
    letI := (NormCurve.constHom (f ≫ s) ⊤).toAlgebra
    letI := (f.appLE U ⊤ e).hom.toAlgebra
    haveI : IsScalarTower k Γ(D, U) Γ(Spec (D.residueField (genericPoint D)), ⊤) :=
      .of_algebraMap_eq' (NormCurve.appLE_comp_constHom s f U ⊤ e).symm
    exact (NormCurve.finite_integralClosure k (NormCurve.surjectiveOnStalks_appLE f hU ⊤ e)).2
      ((ringKrullDim_quotient_le _).trans (ProperCurve.ringKrullDim_eq_one hd hU hxU hx).le)
  have hξ : genericPoint D ∈ Set.range c := by
    refine ⟨f.toNormalization (Nonempty.some inferInstance), ?_⟩
    rw [← Scheme.Hom.comp_apply, f.toNormalization_fromNormalization, Scheme.fromSpecResidueField_apply]
  have hs : Function.Surjective c := fun y =>
    (genericPoint_specializes y).mem_closed c.isClosedMap.isClosed_range hξ
  have hη : c (genericPoint _) = genericPoint D := by
    obtain ⟨y, hy⟩ := hξ
    refine ((genericPoint_specializes _).antisymm ?_).eq.symm
    exact ((genericPoint_specializes y).map c.continuous).trans (specializes_of_eq hy)
  exact ⟨f.normalization, inferInstance, c, inferInstance, hη,
    ((Published.dim_le_of_isIntegralHom c).antisymm (PosBaseChange.dim_le_of_isClosedMap c.isClosedMap hs)).trans hd,
    CurveThrough.smooth_of_dedekind_charts k _ _ (NormCurve.isDedekindDomain_sections f s htr)⟩

def CurveTest (K : Type) [Field K] {X : Scheme.{0}} (L : LB X) : Prop :=
  ∀ (C : Scheme.{0}) [Algebra K Γ(C, ⊤)], SmoothOfRelativeDimension 1 (strHom K (X := C)) → IsProjOver (strHom K (X := C)) →
    GeometricallyConnected (strHom K (X := C)) → ∀ g : C ⟶ X, 0 ≤ interNum K (structureModule C) ![L.pull g]

theorem CurveTest.pull {K : Type} [Field K] {X Y : Scheme.{0}} {L : LB X} (h : CurveTest K L) (hL : L.IsLB)
    (π : Y ⟶ X) : CurveTest K (L.pull π) := fun C _ hs hp hc g => by
  refine (h C hs hp hc (g ≫ π)).trans_eq (interNum_congr_cls K _ (isLB_vecOne (LB.isLB_pull hL _))
    (isLB_vecOne (LB.isLB_pull (LB.isLB_pull hL _) _)) fun j => ?_)
  fin_cases j
  exact pull_comp g π (cls L hL)

theorem CurveTest.isNef_of_isAlgClosed {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}} [Algebra K Γ(X, ⊤)]
    {L : LB X} (h : CurveTest K L) (hL : L.IsLB) : IsNef K L := by
  refine isNef_iff_isClosedImmersion.2 ⟨hL, fun D i _ _ hd hp => ?_⟩
  letI := algebraΓAlong K i
  have hi := appTop_algebraMap_along K i
  rw [comp_strHom hi] at hp
  obtain ⟨C, _, f, _, hη, hdC, hs⟩ := exists_smooth_finite (strHom K D) hd
  letI := algebraΓAlong K f
  have hf := appTop_algebraMap_along K f
  have hpC : IsProper (f ≫ strHom K D) := inferInstance
  rw [comp_strHom hf] at hs hpC
  have hM := LB.isLB_pull hL i
  have h₀ := h.pull hL i C (smoothOfRelativeDimension_one _ hdC) (ProperCurve.isProjOver_of_isProper _ hdC)
    (geometricallyConnected_of_isAlgClosed _) f
  have e₁ := ProjFin.interNumOn_eq_residueDegree_mul K D C f (ProperCurve.isProjOver_of_isProper _ hd) hd hη _ hM
  rw [interNumOn_eq_interNum_pull hf (isLB_vecOne hM)] at e₁
  rw [interNumOn_eq_interNum_pull hi (isLB_vecOne hL)]
  have hdeg : 0 < f.residueDegree (genericPoint C) := Nat.pos_of_ne_zero
    ((PullbackFinitePoint.residueDegree_ne_zero_iff_finite f _).2 (residueFieldMap_finite_of_locallyQuasiFinite f _))
  have e₂ : (fun j => ((![L.pull i] : Fin 1 → LB D) j).pull f) = ![(L.pull i).pull f] :=
    funext fun j => by fin_cases j; rfl
  have e₃ : (fun j => ((![L] : Fin 1 → LB X) j).pull i) = ![L.pull i] := funext fun j => by fin_cases j; rfl
  rw [e₂] at e₁
  rw [e₃]
  rw [e₁] at h₀
  exact nonneg_of_mul_nonneg_right h₀ (by exact_mod_cast hdeg)

theorem CurveTest.isNef (hN : Published.NefProductNonneg) {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)]
    {L : LB X} (h : CurveTest (AlgebraicClosure k) L) (hL : L.IsLB) : IsNef k L := by
  refine isNef_iff_isClosedImmersion.2 ⟨hL, fun D i _ _ hd hp => ?_⟩
  letI := algebraΓAlong k i
  have hi := appTop_algebraMap_along k i
  rw [comp_strHom hi] at hp
  have hM := LB.isLB_pull hL i
  obtain ⟨D', _, π, hp', hd', -, -, he⟩ :=
    Published.exists_algClosed_baseChange (ProperCurve.isProjOver_of_isProper (strHom k D) hd)
  rw [interNumOn_eq_interNum_pull hi (isLB_vecOne hL), ← he 1 _ fun j => LB.isLB_pull (isLB_vecOne hL j) i]
  refine hN _ D' 1 hp' (hd'.trans hd) _ fun j => ?_
  fin_cases j
  exact ((h.pull hL i).pull hM π).isNef_of_isAlgClosed (LB.isLB_pull hM π)

end GlobalTheory.NefCurveTest
end
end
