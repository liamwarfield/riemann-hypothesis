module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
public import Development.WeilBound.ThetaLifts.CartanFactorisation.EqOfInner

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.CartanFactorisation.ArchimedeanUnitIdempotentSmulMixedSpaceVecPairAs
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical

noncomputable section

namespace PositivityTheory.ThKF.W

section One

section Gen

variable {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {JA : Matrix α α E} {JB : Matrix β β E}

def actLin (p : GlobalTheory.WeilM.UG c JA × GlobalTheory.WeilM.UG c JB) : Matrix α β E ≃ₗ[R] Matrix α β E where
  toFun x := GlobalTheory.WeilM.actAB c p x
  invFun x := (((p.1⁻¹ : GlobalTheory.WeilM.UG c JA) : GL α E) : Matrix α α E) * x *
    (((p.2⁻¹ : GlobalTheory.WeilM.UG c JB) : GL β E) : Matrix β β E)ᵀ
  map_add' x y := by simp [GlobalTheory.WeilM.actAB, Matrix.mul_add, Matrix.add_mul]
  map_smul' r x := by simp [GlobalTheory.WeilM.actAB, Matrix.mul_smul, Matrix.smul_mul]
  left_inv x := by
    simp only [GlobalTheory.WeilM.actAB, Subgroup.coe_inv, ← Matrix.mul_assoc]
    rw [Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one,
      Matrix.mul_one]
  right_inv x := by
    simp only [GlobalTheory.WeilM.actAB, Subgroup.coe_inv, ← Matrix.mul_assoc]
    rw [Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one,
      Matrix.mul_one]

theorem actLin_apply (p : GlobalTheory.WeilM.UG c JA × GlobalTheory.WeilM.UG c JB) (x : Matrix α β E) :
    actLin (R := R) c p x = GlobalTheory.WeilM.actAB c p x := rfl

end Gen

variable (F : Type) [Field F] [NumberField F]

def finE {κ : Type} (y : κ → FiniteAdeleRing (𝓞 F) F) : κ → AdeleRing (𝓞 F) F := fun i => (0, y i)

def finE2 {κ : Type} (m : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)) :
    (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F) := (finE F m.1, finE F m.2)

def infE {κ : Type} (z : κ → mixedEmbedding.mixedSpace F) : κ → AdeleRing (𝓞 F) F :=
  fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (z i), 0)

def mixedSpaceVecPairAsAdeles {κ : Type} (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F) := (infE F v.1, infE F v.2)

def slice {κ : Type} (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    (κ → mixedEmbedding.mixedSpace F) → ℂ :=
  fun z => Φ fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (z i), y i)

def schrInf (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) {κ : Type} [Fintype κ]
    (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))
    (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) : (κ → mixedEmbedding.mixedSpace F) → ℂ :=
  fun z => ψ (infE F z ⬝ᵥ infE F v.2 + ⅟(2 : AdeleRing (𝓞 F) F) * (infE F v.1 ⬝ᵥ infE F v.2)) * f (z + v.1)

variable {F}

theorem dot_infE {κ : Type} [Fintype κ] (x : κ → AdeleRing (𝓞 F) F) (z : κ → mixedEmbedding.mixedSpace F) :
    x ⬝ᵥ infE F z = infE F (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) ⬝ᵥ infE F z := by
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Prod.ext ?_ ?_
  · show (x i).1 * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (z i) = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (z i)
    rw [RingEquiv.symm_apply_apply]
  · show (x i).2 * 0 = 0 * 0
    rw [mul_zero, mul_zero]

theorem pureA_schrInf (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) {κ : Type} [Fintype κ]
    (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))
    (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    GlobalTheory.WeilM.pureA F (schrInf F ψ v f) g = GlobalTheory.WeilM.schr ψ (mixedSpaceVecPairAsAdeles F v) (GlobalTheory.WeilM.pureA F f g) := by
  funext x
  simp only [GlobalTheory.WeilM.pureA, schrInf, GlobalTheory.WeilM.schr, mixedSpaceVecPairAsAdeles]
  rw [dot_infE x v.2, mul_assoc]
  have h1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) + v.1 =
      fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + infE F v.1) i).1 := by
    funext i
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 + v.1 i =
      InfiniteAdeleRing.ringEquiv_mixedSpace F ((x i).1 + (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (v.1 i))
    rw [map_add (f := _), RingEquiv.apply_symm_apply]
  have h2 : (fun i => (x i).2) = fun i => ((x + infE F v.1) i).2 := by
    funext i
    show (x i).2 = (x i).2 + 0
    rw [add_zero]
  rw [h1, h2]

theorem pureA_add {κ : Type} (f f' : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    GlobalTheory.WeilM.pureA F (f + f') g = GlobalTheory.WeilM.pureA F f g + GlobalTheory.WeilM.pureA F f' g := by
  funext x
  exact add_mul _ _ _

theorem pureA_smul {κ : Type} (a : ℂ) (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    GlobalTheory.WeilM.pureA F (a • f) g = a • GlobalTheory.WeilM.pureA F f g := by
  funext x
  exact mul_assoc _ _ _

theorem exists_schwartz_slice {κ : Type} [Fintype κ] (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ)
    (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    ∃ s : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, ∀ z, s z = slice F Φ y z := by
  induction hΦ using Submodule.span_induction with
  | mem Ψ hΨ =>
    obtain ⟨f, g, -, rfl⟩ := hΨ
    refine ⟨g y • f, fun z => ?_⟩
    have hz : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (z i))) = z := funext fun i => RingEquiv.apply_symm_apply _ _
    rw [SchwartzMap.smul_apply, smul_eq_mul]
    show g y * f z = f (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (z i))) * g (fun i => y i)
    rw [hz, mul_comm]
  | zero => exact ⟨0, fun z => rfl⟩
  | add Ψ Ψ' _ _ hΨ hΨ' =>
    obtain ⟨s, hs⟩ := hΨ
    obtain ⟨s', hs'⟩ := hΨ'
    exact ⟨s + s', fun z => by rw [SchwartzMap.add_apply, hs z, hs' z]; rfl⟩
  | smul c Ψ _ hΨ =>
    obtain ⟨s, hs⟩ := hΨ
    exact ⟨c • s, fun z => by rw [SchwartzMap.smul_apply, hs z]; rfl⟩

end One

section Two

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def infPart (w : κ → AdeleRing (𝓞 F) F) : κ → mixedEmbedding.mixedSpace F :=
  fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (w i).1

theorem infPart_infE (z : κ → mixedEmbedding.mixedSpace F) : infPart (infE F z) = z := by
  funext i
  exact RingEquiv.apply_symm_apply _ _

theorem infE_infPart (w : κ → AdeleRing (𝓞 F) F) (h : ∀ i, (w i).2 = 0) : infE F (infPart w) = w := by
  funext i
  refine Prod.ext ?_ ?_
  · exact RingEquiv.symm_apply_apply _ _
  · exact (h i).symm

def eInf : AdeleRing (𝓞 F) F := ((1 : InfiniteAdeleRing F), (0 : FiniteAdeleRing (𝓞 F) F))

theorem eInf_smul_snd (w : κ → AdeleRing (𝓞 F) F) (i : κ) : ((eInf (F := F) • w) i).2 = 0 := by
  show (0 : FiniteAdeleRing (𝓞 F) F) * (w i).2 = 0
  exact zero_mul _

theorem eInf_smul_infE (z : κ → mixedEmbedding.mixedSpace F) : eInf (F := F) • infE F z = infE F z := by
  funext i
  refine Prod.ext ?_ ?_
  · exact one_mul _
  · exact zero_mul _

theorem infE_add (z z' : κ → mixedEmbedding.mixedSpace F) : infE F (z + z') = infE F z + infE F z' := by
  funext i
  refine Prod.ext ?_ ?_
  · exact map_add _ _ _
  · exact (add_zero 0).symm

theorem infPart_add (w w' : κ → AdeleRing (𝓞 F) F) : infPart (w + w') = infPart w + infPart w' := by
  funext i
  exact map_add _ _ _

def rAd (t : ℝ) : AdeleRing (𝓞 F) F :=
  ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t • (1 : mixedEmbedding.mixedSpace F)), 0)

theorem infE_smul (t : ℝ) (z : κ → mixedEmbedding.mixedSpace F) : infE F (t • z) = rAd (F := F) t • infE F z := by
  funext i
  refine Prod.ext ?_ ?_
  · show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t • z i) = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t • 1) * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (z i)
    rw [← map_mul, smul_one_mul]
  · exact (mul_zero 0).symm

theorem infPart_smul (t : ℝ) (w : κ → AdeleRing (𝓞 F) F) : infPart (rAd (F := F) t • w) = t • infPart w := by
  funext i
  show InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t • 1) * (w i).1) = t • InfiniteAdeleRing.ringEquiv_mixedSpace F (w i).1
  rw [map_mul, RingEquiv.apply_symm_apply, smul_one_mul]

def infPart2 (w : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) :
    (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F) := (infPart w.1, infPart w.2)

theorem archimedeanPartAdeleTuplePair_mixedSpaceVecPairAsAdeles (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    infPart2 (mixedSpaceVecPairAsAdeles F v) = v := by
  exact Prod.ext (infPart_infE _) (infPart_infE _)

theorem archimedeanUnitIdempotent_smul_mixedSpaceVecPairAsAdeles (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    eInf (F := F) • mixedSpaceVecPairAsAdeles F v = mixedSpaceVecPairAsAdeles F v := by
  exact Prod.ext (eInf_smul_infE _) (eInf_smul_infE _)

theorem mixedSpaceVecPair_archimedeanPart_idempotent_smul (w : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) :
    mixedSpaceVecPairAsAdeles F (infPart2 (eInf (F := F) • w)) = eInf (F := F) • w := by
  exact Prod.ext (infE_infPart _ (eInf_smul_snd _)) (infE_infPart _ (eInf_smul_snd _))

theorem mixedSpaceVecPairAsAdeles_add (v v' : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    mixedSpaceVecPairAsAdeles F (v + v') = mixedSpaceVecPairAsAdeles F v + mixedSpaceVecPairAsAdeles F v' := by
  exact Prod.ext (infE_add _ _) (infE_add _ _)

theorem mixedSpaceVecPairAsAdeles_real_smul (t : ℝ) (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    mixedSpaceVecPairAsAdeles F (t • v) = rAd (F := F) t • mixedSpaceVecPairAsAdeles F v := by
  exact Prod.ext (infE_smul _ _) (infE_smul _ _)

theorem infPart2_add (w w' : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) :
    infPart2 (w + w') = infPart2 w + infPart2 w' := by
  exact Prod.ext (infPart_add _ _) (infPart_add _ _)

theorem infPart2_smul (t : ℝ) (w : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) :
    infPart2 (rAd (F := F) t • w) = t • infPart2 w := by
  exact Prod.ext (infPart_smul _ _) (infPart_smul _ _)

theorem exists_infLin (B : ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) ≃ₗ[AdeleRing (𝓞 F) F]
      ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F))) :
    ∃ L : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) ≃ₗ[ℝ]
        ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)),
      ∀ v, B (mixedSpaceVecPairAsAdeles F v) = mixedSpaceVecPairAsAdeles F (L v) := by
  have key : ∀ (C : ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) ≃ₗ[AdeleRing (𝓞 F) F]
      ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)))
      (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)),
      mixedSpaceVecPairAsAdeles F (infPart2 (C (mixedSpaceVecPairAsAdeles F v))) = C (mixedSpaceVecPairAsAdeles F v) := by
    intro C v
    have h := mixedSpaceVecPair_archimedeanPart_idempotent_smul (C (mixedSpaceVecPairAsAdeles F v))
    rw [← map_smul C eInf (mixedSpaceVecPairAsAdeles F v), archimedeanUnitIdempotent_smul_mixedSpaceVecPairAsAdeles] at h
    exact h
  refine ⟨{ toFun := fun v => infPart2 (B (mixedSpaceVecPairAsAdeles F v))
            invFun := fun v => infPart2 (B.symm (mixedSpaceVecPairAsAdeles F v))
            map_add' := fun v v' => by
              rw [mixedSpaceVecPairAsAdeles_add, map_add (f := _), infPart2_add]
            map_smul' := fun t v => by
              rw [mixedSpaceVecPairAsAdeles_real_smul, map_smul, infPart2_smul, RingHom.id_apply]
            left_inv := fun v => by
              show infPart2 (B.symm (mixedSpaceVecPairAsAdeles F (infPart2 (B (mixedSpaceVecPairAsAdeles F v))))) = v
              rw [key B v, LinearEquiv.symm_apply_apply, archimedeanPartAdeleTuplePair_mixedSpaceVecPairAsAdeles]
            right_inv := fun v => by
              show infPart2 (B (mixedSpaceVecPairAsAdeles F (infPart2 (B.symm (mixedSpaceVecPairAsAdeles F v))))) = v
              rw [key B.symm v, LinearEquiv.apply_symm_apply, archimedeanPartAdeleTuplePair_mixedSpaceVecPairAsAdeles] }, fun v => ?_⟩
  exact (key B v).symm

end Two

namespace HaarSplit

variable (F : Type) [Field F] [NumberField F] (κ : Type)

def splitE : ((κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) ≃+ (κ → AdeleRing (𝓞 F) F) where
  toFun p := fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i)
  invFun x := (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1, fun i => (x i).2)
  left_inv p := Prod.ext (funext fun i => RingEquiv.apply_symm_apply _ _) (funext fun i => rfl)
  right_inv x := funext fun i => Prod.ext (RingEquiv.symm_apply_apply _ _) rfl
  map_add' p q := funext fun i => Prod.ext (map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i) (q.1 i)) rfl

theorem continuous_splitE : Continuous (splitE F κ) := by
  have hs : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
    refine continuous_pi fun v => ?_
    by_cases hv : v.IsReal
    · refine (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.isInducing.continuous_iff.2 ?_
      have h : (InfinitePlace.Completion.extensionEmbeddingOfIsReal hv) ∘ (fun y => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm y) v) =
          fun y => y.1 ⟨v, hv⟩ := by
        funext y
        have h1 := congrArg (fun p : mixedEmbedding.mixedSpace F => p.1 ⟨v, hv⟩) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)
        simpa only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply, Function.comp_apply] using h1
      rw [h]
      exact (continuous_apply _).comp continuous_fst
    · have hc : v.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hv
      refine (InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.isInducing.continuous_iff.2 ?_
      have h : (InfinitePlace.Completion.extensionEmbedding v) ∘ (fun y => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm y) v) =
          fun y => y.2 ⟨v, hc⟩ := by
        funext y
        have h1 := congrArg (fun p : mixedEmbedding.mixedSpace F => p.2 ⟨v, hc⟩) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)
        simpa only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply, Function.comp_apply] using h1
      rw [h]
      exact (continuous_apply _).comp continuous_snd
  show Continuous fun p : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F) =>
    fun i => (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i) : AdeleRing (𝓞 F) F)
  exact continuous_pi fun i => (hs.comp ((continuous_apply i).comp continuous_fst)).prodMk
    ((continuous_apply i).comp continuous_snd)

theorem continuous_splitE_symm : Continuous (splitE F κ).symm := by
  have he : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
    rw [show ⇑(InfiniteAdeleRing.ringEquiv_mixedSpace F) = _ from funext (InfiniteAdeleRing.ringEquiv_mixedSpace_apply F)]
    exact (continuous_pi fun v => (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
      (continuous_apply _)).prodMk (continuous_pi fun v =>
        (InfinitePlace.Completion.isometry_extensionEmbedding _).continuous.comp (continuous_apply _))
  show Continuous fun x : κ → AdeleRing (𝓞 F) F =>
    ((fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1, fun i => (x i).2) : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F))
  exact (continuous_pi fun i => he.comp (continuous_fst.comp (continuous_apply i))).prodMk
    (continuous_pi fun i => continuous_snd.comp (continuous_apply i))

theorem pureA_splitE (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (p : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) :
    GlobalTheory.WeilM.pureA F f g (splitE F κ p) = f p.1 * g p.2 := by
  show f (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i))) * g (fun i => p.2 i) = f p.1 * g p.2
  simp only [RingEquiv.apply_symm_apply]

theorem volume_isAddHaar [Fintype κ] : (volume : Measure (κ → mixedEmbedding.mixedSpace F)).IsAddHaarMeasure := by
  haveI : MeasurableAdd (mixedEmbedding.mixedSpace F) := inferInstance
  haveI : (volume : Measure (mixedEmbedding.mixedSpace F)).IsAddHaarMeasure := inferInstance
  haveI : SigmaFinite (volume : Measure (mixedEmbedding.mixedSpace F)) := inferInstance
  exact MeasureTheory.Measure.pi.isAddHaarMeasure (fun _ => volume)

end HaarSplit

end PositivityTheory.ThKF.W

end
end

noncomputable section

namespace PositivityTheory.ThKF.A

open scoped TensorProduct NNReal ENNReal Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Real RealInnerProductSpace Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels PositivityTheory.ThKF.W GlobalTheory.HeisSchA

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem exists_sb_one : ∃ g ∈ SB (κ → Af F), g 0 = 1 := by
  haveI : LocallyCompactSpace (Af F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI : T2Space (Af F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  haveI := nonarch_finiteAdeleRing (F := F)
  haveI : NonarchimedeanAddGroup (κ → Af F) := nonarch_pi
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : κ → Af F)
  obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean K hK0
  have hc : IsCompact (V : Set (κ → Af F)) := hK.of_isClosed_subset V.isClosed hV
  refine ⟨(V : Set (κ → Af F)).indicator fun _ => 1, ⟨(LocallyConstant.indicator (LocallyConstant.const _ (1 : ℂ))
    V.isClopen).isLocallyConstant, HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩,
    Set.indicator_of_mem V.zero_mem _⟩

theorem exists_char_ne {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {z : κ → Af F} (hz : z ≠ 0) :
    ∃ w : κ → Af F, finChar ψ (z ⬝ᵥ w) ≠ 1 := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hz
  have : ∃ v, evalV F v (z i) ≠ 0 := by
    by_contra h
    push Not at h
    exact hi (af_ext fun u => by rw [h u]; simp)
  obtain ⟨v, hv⟩ := this
  obtain ⟨t, ht⟩ := DFunLike.ne_iff.1 (GlobalTheory.PsiNontriv.psiAt_ne_one ψ hψ v)
  refine ⟨Pi.single i (singleFin v (t / evalV F v (z i))), ?_⟩
  have e : z i * singleFin v (t / evalV F v (z i)) = singleFin v t := af_ext fun u => by
    by_cases h : u = v
    · subst h
      rw [map_mul, evalV_singleFin_self, evalV_singleFin_self, mul_div_cancel₀ _ hv]
    · rw [map_mul, evalV_singleFin_ne h, evalV_singleFin_ne h, mul_zero]
  rw [dotProduct_single, e]
  exact ht

theorem finE_dot (x : κ → AF F) (w : κ → Af F) : x ⬝ᵥ finE F w = ((0, (fun i => (x i).2) ⬝ᵥ w) : AF F) := by
  simp only [dotProduct, finE]
  refine Prod.ext ?_ ?_
  · exact (map_sum (p1 (F := F)) _ _).trans (Finset.sum_eq_zero fun i _ => mul_zero (x i).1)
  · exact map_sum (p2 (F := F)) _ _

theorem schr_mod (ψ : AddChar (AF F) ℂ) (w : κ → Af F) (Φ : (κ → AF F) → ℂ) (x : κ → AF F) :
    schr ψ (finE2 F (0, w)) Φ x = finChar ψ ((fun i => (x i).2) ⬝ᵥ w) * Φ x := by
  have : finE F (0 : κ → Af F) = 0 := rfl
  simp only [schr, finE2, this, zero_dotProduct, mul_zero, add_zero]
  rw [finE_dot]
  rfl

theorem schr_tr (ψ : AddChar (AF F) ℂ) (z : κ → Af F) (Φ : (κ → AF F) → ℂ) (x : κ → AF F) :
    schr ψ (finE2 F (z, 0)) Φ x = Φ (x + finE F z) := by
  have : finE F (0 : κ → Af F) = 0 := rfl
  simp [schr, finE2, this]

theorem pureA_mem (f : SInf F κ) {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) : pureA F f g ∈ schA F κ :=
  Submodule.subset_span ⟨f, g, hg, rfl⟩

theorem apply_pure {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (S : Module.End ℂ ((κ → AF F) → ℂ))
    (hS : ∀ m, ∀ Φ ∈ schA F κ, S (schr ψ (finE2 F m) Φ) = schr ψ (finE2 F m) (S Φ)) (f : SInf F κ)
    {g₀ : (κ → Af F) → ℂ} (h₀ : g₀ ∈ SB (κ → Af F)) (h₁ : g₀ 0 = 1) {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) :
    S (pureA F f g) = pureA F (slice F (S (pureA F f g₀)) 0) g := by
  classical
  haveI : T2Space (Af F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  let L : ((κ → Af F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) :=
    { toFun := fun g => pureA F f g
      map_add' := fun a b => funext fun x => by simp [pureA, mul_add]
      map_smul' := fun c a => funext fun x => by simp [pureA, mul_left_comm] }
  have key : ∀ φ ∈ SB (κ → Af F), φ 0 = 0 → ∀ y, S (pureA F f φ) (infE F y) = 0 := fun φ hφ h0 y => by
    let e : (κ → Af F) → (κ → Af F) → ℂ := fun w z => finChar ψ (z ⬝ᵥ w) - 1
    have he : ∀ w, IsLocallyConstant (e w) := fun w =>
      ((finChar_isLocallyConstant ψ hψ.1).comp_continuous (continuous_id.dotProduct continuous_const)).comp (· - 1)
    have hts : tsupport φ = Function.support φ := by
      refine IsClosed.closure_eq ⟨?_⟩
      have := hφ.1.isOpen_fiber 0
      convert this using 1
      ext x
      simp
    have hex : ∀ z : tsupport φ, ∃ w, e w z ≠ 0 := fun z => by
      have hz : (z : κ → Af F) ≠ 0 := fun h => by
        have : (z : κ → Af F) ∈ Function.support φ := hts ▸ z.2
        exact this (h ▸ h0)
      obtain ⟨w, hw⟩ := exists_char_ne hψ hz
      exact ⟨w, sub_ne_zero.2 hw⟩
    choose w hw using hex
    obtain ⟨t, ht⟩ := (hφ.2 : IsCompact (tsupport φ)).elim_nhds_subcover' (fun z hz => {x | e (w ⟨z, hz⟩) x ≠ 0})
      fun z hz => ((he _).continuous.isOpen_preimage _ isOpen_ne).mem_nhds (hw ⟨z, hz⟩)
    let G : (κ → Af F) → ℂ := fun x => ∑ z ∈ t, e (w z) x * (starRingEnd ℂ) (e (w z) x)
    have hG : IsLocallyConstant G := by
      rw [IsLocallyConstant.iff_eventually_eq]
      intro x
      filter_upwards [(Filter.eventually_all_finset t).2 fun z _ => (he (w z)).eventually_eq x] with y hy
      exact Finset.sum_congr rfl fun z hz => by rw [hy z hz]
    have hG0 : ∀ x, φ x ≠ 0 → G x ≠ 0 := fun x hx => by
      obtain ⟨z, hz, hzx⟩ : ∃ z ∈ t, e (w z) x ≠ 0 := by simpa using ht (subset_tsupport _ hx)
      simp only [G, Complex.mul_conj]
      rw [← Complex.ofReal_sum, Complex.ofReal_ne_zero]
      exact (Finset.sum_pos' (f := fun i => Complex.normSq (e (w i) x)) (fun _ _ => Complex.normSq_nonneg _) ⟨z, hz, Complex.normSq_pos.2 hzx⟩).ne'
    let φ' : tsupport φ → (κ → Af F) → ℂ := fun z x => (starRingEnd ℂ) (e (w z) x) * (G x)⁻¹ * φ x
    have hφ' : ∀ z, φ' z ∈ SB (κ → Af F) := fun z =>
      ⟨((((he (w z)).comp (starRingEnd ℂ)).mul (hG.comp (·⁻¹))).mul hφ.1), hφ.2.mul_left⟩
    have hsum : pureA F f φ = ∑ z ∈ t, (schr ψ (finE2 F (0, w z)) (pureA F f (φ' z)) - pureA F f (φ' z)) := by
      funext x
      simp only [Finset.sum_apply, Pi.sub_apply, schr_mod, pureA, φ']
      by_cases hx : φ (fun i => (x i).2) = 0
      · simp [hx]
      · have := hG0 _ hx
        have e2 : ∀ (a b c d k : ℂ), a * (k * (b * c * d)) - k * (b * c * d) = ((a - 1) * b) * (k * c * d) := fun _ _ _ _ _ => by
          ring
        simp only [e2, ← Finset.sum_mul]
        change _ = G _ * _
        field_simp
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum, map_sum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun z _ => ?_
    rw [map_sub, hS _ _ (pureA_mem f (hφ' z)), Pi.sub_apply, schr_mod]
    have : (fun i => (infE F y i).2) = 0 := rfl
    rw [this, zero_dotProduct, AddChar.map_zero_eq_one, one_mul, sub_self]
  funext x
  set z : κ → Af F := fun i => (x i).2 with hz
  set y := infPart x with hy
  have hx : x = infE F y + finE F z := funext fun i => Prod.ext
    (by show _ = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _ + 0
        rw [add_zero]; exact (RingEquiv.symm_apply_apply _ _).symm) (zero_add (x i).2).symm
  have hg' : (fun u => g (u + z)) ∈ SB (κ → Af F) :=
    ⟨hg.1.comp_continuous (continuous_id.add continuous_const), hg.2.comp_homeomorph (Homeomorph.addRight z)⟩
  have e1 : schr ψ (finE2 F (z, 0)) (pureA F f g) = pureA F f fun u => g (u + z) := funext fun a => by
    rw [schr_tr]
    simp only [pureA]
    congr 2
    funext i
    exact congrArg _ (add_zero _)
  have e2 := key _ (sub_mem hg' (Submodule.smul_mem _ (g z) h₀)) (by simp [h₁]) y
  have e3 : pureA F f ((fun u => g (u + z)) - g z • g₀) = pureA F f (fun u => g (u + z)) - g z • pureA F f g₀ := by
    have := map_sub L (fun u => g (u + z)) (g z • g₀)
    rw [map_smul] at this
    exact this
  rw [e3, map_sub, map_smul, ← e1, hS _ _ (pureA_mem f hg), Pi.sub_apply, schr_tr, ← hx, sub_eq_zero] at e2
  rw [e2, Pi.smul_apply, smul_eq_mul, mul_comm]
  rfl

theorem pureA_inj {f f' : (κ → mixedEmbedding.mixedSpace F) → ℂ} {g : (κ → Af F) → ℂ} (hg : g 0 = 1)
    (h : pureA F f g = pureA F f' g) : f = f' := funext fun y => by
  have := congrFun h (infE F y)
  have e : (fun i => (infE F y i).2) = 0 := rfl
  have e' : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (infE F y i).1) = y := infPart_infE y
  simpa only [pureA, e, e', hg, mul_one] using this

theorem exists_lin {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (S : Module.End ℂ ((κ → AF F) → ℂ))
    (hp : ∀ Φ ∈ schA F κ, S Φ ∈ schA F κ)
    (hS : ∀ m, ∀ Φ ∈ schA F κ, S (schr ψ (finE2 F m) Φ) = schr ψ (finE2 F m) (S Φ)) :
    ∃ T : SInf F κ →ₗ[ℂ] SInf F κ, ∀ f : SInf F κ, ∀ g ∈ SB (κ → Af F), S (pureA F f g) = pureA F (T f) g := by
  obtain ⟨g₀, h₀, h₁⟩ := exists_sb_one (F := F) (κ := κ)
  choose T hT using fun f : SInf F κ => exists_schwartz_slice _ (hp _ (pureA_mem f h₀)) 0
  have h : ∀ f : SInf F κ, ∀ g ∈ SB (κ → Af F), S (pureA F f g) = pureA F (T f) g := fun f g hg => by
    rw [apply_pure hψ S hS f h₀ h₁ hg, show ⇑(T f) = _ from funext (hT f)]
  refine ⟨⟨⟨T, fun a b => DFunLike.coe_injective (pureA_inj h₁ ?_)⟩, fun c a => DFunLike.coe_injective (pureA_inj h₁ ?_)⟩, h⟩
  · rw [← h _ _ h₀, show ⇑(a + b) = ⇑a + ⇑b from rfl, pureA_add, map_add (f := _), h _ _ h₀, h _ _ h₀, ← pureA_add]
    rfl
  · rw [← h _ _ h₀, show ⇑(c • a) = c • ⇑a from rfl, pureA_smul, map_smul, h _ _ h₀, ← pureA_smul]
    rfl

theorem lintegral_eq {S : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ}
    (hU : ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ φ ∈ schA F κ, ∫⁻ x, ‖S φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) {f f' : SInf F κ}
    (h : ∀ g ∈ SB (κ → Af F), S (pureA F f g) = pureA F f' g) : ∫⁻ x, ‖f' x‖ₑ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 := by
  obtain ⟨g, hg, h₁⟩ := exists_sb_one (F := F) (κ := κ)
  haveI := HaarSplit.volume_isAddHaar F κ
  haveI : OpensMeasurableSpace (κ → mixedEmbedding.mixedSpace F) := inferInstance
  haveI : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI : SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  letI mY : MeasurableSpace (κ → FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  letI mA : MeasurableSpace (κ → AdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → AdeleRing (𝓞 F) F) := ⟨rfl⟩
  haveI : SigmaCompactSpace (κ → FiniteAdeleRing (𝓞 F) F) := sigmaCompactSpace_of_locallyCompact_secondCountable
  set ν : Measure (κ → FiniteAdeleRing (𝓞 F) F) := Measure.addHaar with hν
  haveI : SFinite ν := inferInstance
  haveI : MeasurableAdd (κ → mixedEmbedding.mixedSpace F) := ContinuousAdd.measurableAdd
  haveI : MeasurableAdd (κ → FiniteAdeleRing (𝓞 F) F) := ContinuousAdd.measurableAdd
  haveI : ν.IsAddHaarMeasure := by rw [hν]; infer_instance
  haveI : ((volume : Measure (κ → mixedEmbedding.mixedSpace F)).prod ν).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure (volume : Measure (κ → mixedEmbedding.mixedSpace F)) ν
  have hμH : Measure.IsAddHaarMeasure ((volume.prod ν).map (HaarSplit.splitE F κ)) :=
    (HaarSplit.splitE F κ).isAddHaarMeasure_map _ (HaarSplit.continuous_splitE F κ) (HaarSplit.continuous_splitE_symm F κ)
  let em : ((κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) ≃ᵐ (κ → AdeleRing (𝓞 F) F) :=
    (Homeomorph.mk (HaarSplit.splitE F κ).toEquiv (HaarSplit.continuous_splitE F κ)
      (HaarSplit.continuous_splitE_symm F κ)).toMeasurableEquiv
  have hint : ∀ h : (κ → AdeleRing (𝓞 F) F) → ℝ≥0∞,
      ∫⁻ x, h x ∂((volume.prod ν).map (HaarSplit.splitE F κ)) = ∫⁻ p, h (HaarSplit.splitE F κ p) ∂(volume.prod ν) :=
    fun h => lintegral_map_equiv h em
  have hgc : Continuous g := hg.1.continuous
  have hC : ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν ≠ ⊤ := by
    have h1 : ∫⁻ y, ‖g y * g y‖ₑ ∂ν < ⊤ :=
      ((hgc.mul hgc).integrable_of_hasCompactSupport (hg.2.mul_left (f := g))).2
    refine ne_of_lt (lt_of_le_of_lt (le_of_eq (lintegral_congr fun y => ?_)) h1)
    rw [enorm_mul, sq]
  have hC0 : ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν ≠ 0 := fun h0 => by
    rw [lintegral_eq_zero_iff (hgc.measurable.enorm.pow_const 2)] at h0
    have h2 : g =ᵐ[ν] 0 := h0.mono fun y hy => by simpa using hy
    have := congrFun ((hgc.ae_eq_iff_eq ν continuous_zero).1 h2) 0
    simp [h₁] at this
  have hp : ∀ a : SInf F κ, ∫⁻ x, ‖pureA F a g x‖ₑ ^ 2 ∂((volume.prod ν).map (HaarSplit.splitE F κ)) =
      (∫⁻ x, ‖a x‖ₑ ^ 2) * ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν := fun a => by
    rw [hint]
    have e1 : ∀ p, ‖pureA F a g (HaarSplit.splitE F κ p)‖ₑ ^ 2 = ‖a p.1‖ₑ ^ 2 * ‖g p.2‖ₑ ^ 2 := by
      intro p
      rw [HaarSplit.pureA_splitE, enorm_mul, mul_pow]
    simp_rw [e1]
    rw [lintegral_prod_mul (a.continuous.measurable.enorm.pow_const 2).aemeasurable
      (hgc.measurable.enorm.pow_const 2).aemeasurable]
  have := hU _ hμH _ (pureA_mem f hg)
  rw [h g hg, hp, hp] at this
  exact (ENNReal.mul_left_inj hC0 hC).1 this

theorem exists_adm (L : SInf F κ →L[ℂ] ℂ) : ∃ l ∈ (adeleClass F).adm κ, ∀ f : SInf F κ, ∀ g ∈ SB (κ → Af F),
    l (pureA F f g) = g 0 * L f := by
  choose s hs using fun Φ : schA F κ => exists_schwartz_slice Φ.1 Φ.2 0
  let s' : schA F κ →ₗ[ℂ] SInf F κ :=
    { toFun := s
      map_add' := fun a b => SchwartzMap.ext fun z => by rw [SchwartzMap.add_apply, hs, hs, hs]; rfl
      map_smul' := fun c a => SchwartzMap.ext fun z => by rw [SchwartzMap.smul_apply, hs, hs]; rfl }
  obtain ⟨l, hl⟩ := LinearMap.exists_extend (L.toLinearMap ∘ₗ s')
  have h : ∀ f : SInf F κ, ∀ g ∈ SB (κ → Af F), l (pureA F f g) = g 0 * L f := fun f g hg => by
    have h1 := LinearMap.congr_fun hl ⟨_, pureA_mem f hg⟩
    have h2 : s ⟨_, pureA_mem f hg⟩ = g 0 • f := SchwartzMap.ext fun z => by
      rw [hs]
      simp only [SchwartzMap.smul_apply, smul_eq_mul, slice, pureA, RingEquiv.apply_symm_apply]
      exact mul_comm _ _
    refine h1.trans ?_
    show L (s _) = _
    rw [h2, map_smul, smul_eq_mul]
  exact ⟨l, fun g hg => ⟨g 0 • L, fun f => h f g hg⟩, h⟩

end PositivityTheory.ThKF.A
