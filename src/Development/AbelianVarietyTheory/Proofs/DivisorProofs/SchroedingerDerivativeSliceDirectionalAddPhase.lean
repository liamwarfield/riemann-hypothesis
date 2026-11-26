module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoBarZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShapeIntegratedOperatorRangesPolynomial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolyCoeffVectorsLieInFiniteDimensionalSmooth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonsplitCentraliserNormElement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorLatticePointOfIntegralSplitPlaceCoor

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerDerivativeSliceDirectionalAddPhase
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerDerivativeSliceDirectionalAddPhase
open IsDedekindDomain NumberField
open scoped Classical

noncomputable section

namespace GlobalTheory.ArchDeriv
variable (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem archimedean_map_add (a b : mixedEmbedding.mixedSpace F) :
    GlobalTheory.WeilL2Words.arch1 F (a + b) = GlobalTheory.WeilL2Words.arch1 F a + GlobalTheory.WeilL2Words.arch1 F b := by
  unfold GlobalTheory.WeilL2Words.arch1
  refine Prod.ext ?_ ?_
  · exact map_add _ a b
  · exact (add_zero (0 : FiniteAdeleRing (𝓞 F) F)).symm

theorem adeleOfMixedSpaceComponent_finsetSum (f : κ → mixedEmbedding.mixedSpace F) :
    GlobalTheory.WeilL2Words.arch1 F (∑ k, f k) = ∑ k, GlobalTheory.WeilL2Words.arch1 F (f k) :=
  map_sum (AddMonoidHom.mk' (GlobalTheory.WeilL2Words.arch1 F) (archimedean_map_add F)) f Finset.univ

theorem adeleJoin_mul_arch1 (x : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) (k : κ)
    (b : mixedEmbedding.mixedSpace F) :
    GlobalTheory.WeilCont.adeleJoin F x y k * GlobalTheory.WeilL2Words.arch1 F b = GlobalTheory.WeilL2Words.arch1 F (x k * b) := by
  unfold GlobalTheory.WeilL2Words.arch1 GlobalTheory.WeilCont.adeleJoin
  refine Prod.ext ?_ ?_
  · exact (map_mul _ (x k) b).symm
  · exact mul_zero (y k)

theorem adeleOfMixedSpaceComponent_mul (a b : mixedEmbedding.mixedSpace F) :
    GlobalTheory.WeilL2Words.arch1 F a * GlobalTheory.WeilL2Words.arch1 F b = GlobalTheory.WeilL2Words.arch1 F (a * b) := by
  unfold GlobalTheory.WeilL2Words.arch1
  refine Prod.ext ?_ ?_
  · exact (map_mul _ a b).symm
  · exact mul_zero (0 : FiniteAdeleRing (𝓞 F) F)

theorem adeleJoin_add_arch (x v : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    GlobalTheory.WeilCont.adeleJoin F x y + GlobalTheory.WeilL2Words.arch F v = GlobalTheory.WeilCont.adeleJoin F (x + v) y := by
  funext i
  refine Prod.ext ?_ ?_
  · exact (map_add _ (x i) (v i)).symm
  · exact add_zero (y i)

theorem adeleJoin_dot_arch (x w : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    GlobalTheory.WeilCont.adeleJoin F x y ⬝ᵥ GlobalTheory.WeilL2Words.arch F w = GlobalTheory.WeilL2Words.arch1 F (∑ k, x k * w k) := by
  rw [adeleOfMixedSpaceComponent_finsetSum]
  unfold dotProduct
  refine Finset.sum_congr rfl fun k _ => ?_
  exact adeleJoin_mul_arch1 F x y k (w k)

theorem arch_dot_arch (v w : κ → mixedEmbedding.mixedSpace F) :
    GlobalTheory.WeilL2Words.arch F v ⬝ᵥ GlobalTheory.WeilL2Words.arch F w = GlobalTheory.WeilL2Words.arch1 F (∑ k, v k * w k) := by
  rw [adeleOfMixedSpaceComponent_finsetSum]
  unfold dotProduct
  refine Finset.sum_congr rfl fun k _ => ?_
  exact adeleOfMixedSpaceComponent_mul F (v k) (w k)

theorem mul_arch1 [Invertible (2 : AdeleRing (𝓞 F) F)] (b : mixedEmbedding.mixedSpace F) :
    ⅟(2 : AdeleRing (𝓞 F) F) * GlobalTheory.WeilL2Words.arch1 F b =
      GlobalTheory.WeilL2Words.arch1 F (InfiniteAdeleRing.ringEquiv_mixedSpace F (⅟(2 : AdeleRing (𝓞 F) F)).1 * b) := by
  unfold GlobalTheory.WeilL2Words.arch1
  refine Prod.ext ?_ ?_
  · show (⅟(2 : AdeleRing (𝓞 F) F)).1 * _ = _
    rw [map_mul, RingEquiv.symm_apply_apply]
  · exact mul_zero _

end GlobalTheory.ArchDeriv

open GlobalTheory.ArchDeriv
namespace GlobalTheory.WeilL2Words

theorem dS_adeleJoin_eq : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ),
    (∀ z, ψ (GlobalTheory.WeilL2Words.arch1 F z) = Complex.exp (2 * Real.pi * Complex.I * ℓ z)) →
    ∀ (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (y : κ → FiniteAdeleRing (𝓞 F) F),
      Differentiable ℝ (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) →
      ∀ (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) (x : κ → mixedEmbedding.mixedSpace F),
        GlobalTheory.WeilL2Words.dS F ψ h Φ (GlobalTheory.WeilCont.adeleJoin F x y) =
          fderiv ℝ (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x h.1 +
            2 * Real.pi * Complex.I * (ℓ (∑ k, x k * h.2 k) : ℂ) * Φ (GlobalTheory.WeilCont.adeleJoin F x y) := by
  intro F _ _ _ κ _ ψ ℓ hψ Φ y hs h x
  set s : (κ → mixedEmbedding.mixedSpace F) → ℂ := fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y) with hs_def
  set P : mixedEmbedding.mixedSpace F := ∑ k, x k * h.2 k with hP
  set Q : mixedEmbedding.mixedSpace F :=
    InfiniteAdeleRing.ringEquiv_mixedSpace F (⅟(2 : AdeleRing (𝓞 F) F)).1 * ∑ k, h.1 k * h.2 k with hQ
  set r : ℝ → ℝ := fun t => t * ℓ P + t ^ 2 * ℓ Q with hr
  have key : (fun t : ℝ => GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair F (t • h)) Φ (GlobalTheory.WeilCont.adeleJoin F x y)) =
      fun t => Complex.exp (2 * Real.pi * Complex.I * (r t : ℂ)) * s (x + t • h.1) := by
    funext t
    have e1 : (t • h).1 = t • h.1 := rfl
    have e2 : (t • h).2 = t • h.2 := rfl
    simp only [GlobalTheory.WeilM.schr, GlobalTheory.WeilL2Words.archPair, e1, e2, adeleJoin_add_arch, adeleJoin_dot_arch, arch_dot_arch,
      mul_arch1, ← archimedean_map_add]
    congr 1
    · rw [hψ]
      congr 2
      have q1 : (∑ k, x k * (t • h.2) k) = t • P := by
        simp only [hP, Pi.smul_apply, mul_smul_comm, Finset.smul_sum]
      have q2 : InfiniteAdeleRing.ringEquiv_mixedSpace F (⅟(2 : AdeleRing (𝓞 F) F)).1 *
          ∑ k, (t • h.1) k * (t • h.2) k = t ^ 2 • Q := by
        simp only [Pi.smul_apply, smul_mul_smul_comm]
        rw [← Finset.smul_sum, mul_smul_comm, hQ, pow_two]
      rw [q1, q2, map_add (f := _), map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have hr' : HasDerivAt r (ℓ P) 0 := by
    have h1 := (hasDerivAt_mul_const (x := (0 : ℝ)) (ℓ P)).add ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (ℓ Q))
    exact h1.congr_deriv (by simp)
  have hE : HasDerivAt (fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * (r t : ℂ)))
      (Complex.exp (2 * Real.pi * Complex.I * (r 0 : ℂ)) * (2 * Real.pi * Complex.I * (ℓ P : ℂ))) 0 :=
    (hr'.ofReal_comp.const_mul (2 * Real.pi * Complex.I)).cexp
  have hc : HasDerivAt (fun t : ℝ => x + t • h.1) h.1 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const h.1).const_add x
  have hS : HasDerivAt (fun t : ℝ => s (x + t • h.1)) (fderiv ℝ s x h.1) 0 := by
    have hf : HasFDerivAt s (fderiv ℝ s x) (x + (0 : ℝ) • h.1) := by
      rw [zero_smul, add_zero]
      exact (hs x).hasFDerivAt
    exact hf.comp_hasDerivAt (0 : ℝ) hc
  have hD := hE.mul hS
  unfold GlobalTheory.WeilL2Words.dS
  rw [key]
  refine hD.deriv.trans ?_
  have r0 : r 0 = 0 := by simp [hr]
  simp only [r0, zero_smul, add_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
  ring

end GlobalTheory.WeilL2Words

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerDerivativeSliceDirectionalAddPhaseStatement
open IsDedekindDomain NumberField
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schroedingerDerivative_slice_directional_add_phase : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ),
    (∀ z, ψ (GlobalTheory.WeilL2Words.arch1 F z) = Complex.exp (2 * Real.pi * Complex.I * ℓ z)) →
    ∀ (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (y : κ → FiniteAdeleRing (𝓞 F) F),
      Differentiable ℝ (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) →
      ∀ (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) (x : κ → mixedEmbedding.mixedSpace F),
        GlobalTheory.WeilL2Words.dS F ψ h Φ (GlobalTheory.WeilCont.adeleJoin F x y) =
          fderiv ℝ (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x h.1 +
            2 * Real.pi * Complex.I * (ℓ (∑ k, x k * h.2 k) : ℂ) * Φ (GlobalTheory.WeilCont.adeleJoin F x y) := by
  first | exact @GlobalTheory.WeilL2Words.dS_adeleJoin_eq | exact GlobalTheory.WeilL2Words.dS_adeleJoin_eq | (intros; apply GlobalTheory.WeilL2Words.dS_adeleJoin_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorForLeviMatrix
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorForLeviMatrix
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.LeviOp

variable {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ]

theorem map_inv_mul {S : Type} [CommRing S] (g : F →+* S) (A : Matrix κ κ F) (h : IsUnit A.det) :
    A⁻¹.map g * A.map g = 1 := by
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul A h, Matrix.map_one g (map_zero g) (map_one g)]

theorem map_mul_inv {S : Type} [CommRing S] (g : F →+* S) (A : Matrix κ κ F) (h : IsUnit A.det) :
    A.map g * A⁻¹.map g = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv A h, Matrix.map_one g (map_zero g) (map_one g)]

theorem hom_mulVec {S T : Type} [CommRing S] [CommRing T] (f : S →+* T) (g : F →+* S) (g' : F →+* T)
    (hg : f.comp g = g') (M : Matrix κ κ F) (x : κ → S) (i : κ) :
    f ((M.map g *ᵥ x) i) = (M.map g' *ᵥ (fun j => f (x j))) i := by
  subst hg
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem spAct_levi {R : Type} [CommRing R] [Algebra F R] (A : Matrix κ κ F) (w : (κ → R) × (κ → R)) :
    GlobalTheory.SympChange.spAct (GlobalTheory.SympChange.leviM A) w =
      (A.map (algebraMap F R) *ᵥ w.1, (A⁻¹.map (algebraMap F R))ᵀ *ᵥ w.2) := by
  unfold GlobalTheory.SympChange.spAct GlobalTheory.SympChange.leviM
  rw [Matrix.fromBlocks_map, Matrix.fromBlocks_mulVec]
  ext k <;> simp [Matrix.transpose_map]

theorem schr_levi {R : Type} [CommRing R] [Algebra F R] [Invertible (2 : R)] (ψ : AddChar R ℂ)
    (A : Matrix κ κ F) (hA : IsUnit A.det) (w : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) :
    (fun x => schr ψ w φ (A⁻¹.map (algebraMap F R) *ᵥ x)) =
      schr ψ (GlobalTheory.SympChange.spAct (GlobalTheory.SympChange.leviM A) w) (fun x => φ (A⁻¹.map (algebraMap F R) *ᵥ x)) := by
  rw [spAct_levi]
  funext x
  simp only [GlobalTheory.WeilM.schr]
  have h1 := map_inv_mul (algebraMap F R) A hA
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec,
    Matrix.dotProduct_mulVec x, Matrix.vecMul_transpose, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
    Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]

def homeo {S : Type} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] (g : F →+* S) (A : Matrix κ κ F)
    (hA : IsUnit A.det) : (κ → S) ≃ₜ (κ → S) where
  toFun x := A⁻¹.map g *ᵥ x
  invFun x := A.map g *ᵥ x
  left_inv x := by simp only [Matrix.mulVec_mulVec, map_mul_inv g A hA, Matrix.one_mulVec]
  right_inv x := by simp only [Matrix.mulVec_mulVec, map_inv_mul g A hA, Matrix.one_mulVec]
  continuous_toFun := Continuous.matrix_mulVec continuous_const continuous_id
  continuous_invFun := Continuous.matrix_mulVec continuous_const continuous_id

theorem homeo_apply {S : Type} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] (g : F →+* S)
    (A : Matrix κ κ F) (hA : IsUnit A.det) (x : κ → S) : homeo g A hA x = A⁻¹.map g *ᵥ x := rfl

def linEquiv {S : Type} [CommRing S] [Algebra ℝ S] [TopologicalSpace S] [IsTopologicalRing S] (g : F →+* S)
    (A : Matrix κ κ F) (hA : IsUnit A.det) : (κ → S) ≃L[ℝ] (κ → S) where
  toFun x := A⁻¹.map g *ᵥ x
  invFun x := A.map g *ᵥ x
  map_add' x y := Matrix.mulVec_add _ x y
  map_smul' c x := Matrix.mulVec_smul _ c x
  left_inv x := by simp only [Matrix.mulVec_mulVec, map_mul_inv g A hA, Matrix.one_mulVec]
  right_inv x := by simp only [Matrix.mulVec_mulVec, map_inv_mul g A hA, Matrix.one_mulVec]
  continuous_toFun := Continuous.matrix_mulVec continuous_const continuous_id
  continuous_invFun := Continuous.matrix_mulVec continuous_const continuous_id

theorem sb_comp {X : Type} [TopologicalSpace X] (h : X ≃ₜ X) {φ : X → ℂ} (hφ : φ ∈ SB X) : φ ∘ h ∈ SB X :=
  ⟨hφ.1.comp_continuous h.continuous, hφ.2.comp_homeomorph h⟩

variable [NumberField F]

def evIr : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

theorem mulVec_mem {v : Pl (F := F)} (M : Matrix κ κ F)
    (hM : ∀ i j, algebraMap F (Fv F v) (M i j) ∈ v.adicCompletionIntegers F) (x : κ → Fv F v)
    (hx : ∀ i, x i ∈ v.adicCompletionIntegers F) (i : κ) :
    (M.map (algebraMap F (Fv F v)) *ᵥ x) i ∈ v.adicCompletionIntegers F := by
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  exact sum_mem fun j _ => mul_mem (hM i j) (hx j)

theorem eventually_int (M : Matrix κ κ F) :
    ∀ᶠ v : Pl F in cofinite, ∀ i j, algebraMap F (Fv F v) (M i j) ∈ v.adicCompletionIntegers F := by
  simp only [Filter.eventually_all]
  exact fun i j => (algebraMap F (Af F) (M i j)).2


open scoped Classical in
theorem hasOp_levi : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → (∀ᶠ v in cofinite, PsiUnr ψ v) →
    (∀ v : Pl (F := F), ∃ x, psiLoc ψ v x ≠ 1) → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (A : Matrix κ κ F), IsUnit A.det →
    GlobalTheory.SympChange.HasOp ψ (GlobalTheory.SympChange.leviM A) := by
  intro F _ _ ψ _ _ _ κ _ _ A hA
  let gI : F →+* mixedEmbedding.mixedSpace F := (evIr (F := F)).comp (algebraMap F (AF F))
  let gF : F →+* FiniteAdeleRing (𝓞 F) F := (RingHom.snd _ _).comp (algebraMap F (AF F))
  let L := linEquiv (κ := κ) gI A hA
  refine ⟨LinearMap.funLeft ℂ ℂ (fun x : κ → AF F => A⁻¹.map (algebraMap F (AF F)) *ᵥ x),
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L,
    fun v => LinearMap.funLeft ℂ ℂ (fun x : κ → Fv F v => A⁻¹.map (algebraMap F (Fv F v)) *ᵥ x),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f
    refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm f, ?_⟩
    refine SchwartzMap.ext fun x => ?_
    simp
  · have key : ∀ (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
        LinearMap.funLeft ℂ ℂ (fun x : κ → AF F => A⁻¹.map (algebraMap F (AF F)) *ᵥ x) (pureA F f g) =
          pureA F (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L f) (g ∘ homeo gF A hA) := by
      intro f g
      funext x
      simp only [LinearMap.funLeft_apply, pureA, Function.comp_apply, homeo_apply,
        SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
      congr 1
      · congr 1
        funext i
        exact hom_mulVec evIr (algebraMap F (AF F)) gI rfl A⁻¹ x i
      · congr 1
        funext i
        exact hom_mulVec (RingHom.snd _ _) (algebraMap F (AF F)) gF rfl A⁻¹ x i
    have hle : schA F κ ≤ (schA F κ).comap
        (LinearMap.funLeft ℂ ℂ (fun x : κ → AF F => A⁻¹.map (algebraMap F (AF F)) *ᵥ x)) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨f, g, hg, rfl⟩
      show _ ∈ schA F κ
      rw [key]
      exact Submodule.subset_span ⟨_, _, sb_comp (homeo gF A hA) hg, rfl⟩
    exact fun Φ hΦ => hle hΦ
  · intro w Φ _
    exact schr_levi ψ A hA w Φ
  · intro v
    refine le_antisymm (Submodule.map_le_iff_le_comap.2 fun φ hφ => sb_comp (homeo _ A hA) hφ) ?_
    intro φ hφ
    refine ⟨φ ∘ (homeo (algebraMap F (Fv F v)) A hA).symm, sb_comp _ hφ, ?_⟩
    funext x
    simp only [LinearMap.funLeft_apply, Function.comp_apply]
    exact congrArg φ ((homeo (algebraMap F (Fv F v)) A hA).symm_apply_apply x)
  · intro v φ _ h
    funext x
    have := congrFun h ((homeo (algebraMap F (Fv F v)) A hA).symm x)
    simp only [LinearMap.funLeft_apply, Pi.zero_apply] at this
    have hx : A⁻¹.map (algebraMap F (Fv F v)) *ᵥ (homeo (algebraMap F (Fv F v)) A hA).symm x = x :=
      (homeo (algebraMap F (Fv F v)) A hA).apply_symm_apply x
    rw [hx] at this
    exact this
  · intro v w φ _
    exact schr_levi (GlobalTheory.LatVac.psiAt ψ v) A hA w φ
  · filter_upwards [eventually_int A, eventually_int A⁻¹] with v hA1 hA2
    funext x
    have hiff : (∀ i, (A⁻¹.map (algebraMap F (Fv F v)) *ᵥ x) i ∈ v.adicCompletionIntegers F) ↔
        ∀ i, x i ∈ v.adicCompletionIntegers F := by
      constructor
      · intro h i
        have e : x = A.map (algebraMap F (Fv F v)) *ᵥ (A⁻¹.map (algebraMap F (Fv F v)) *ᵥ x) :=
          ((homeo (algebraMap F (Fv F v)) A hA).symm_apply_apply x).symm
        rw [e]
        exact mulVec_mem A hA1 _ h i
      · intro h i
        exact mulVec_mem A⁻¹ hA2 x h i
    show Set.indicator _ _ _ = Set.indicator _ _ _
    by_cases hx : ∀ i, x i ∈ v.adicCompletionIntegers F
    · rw [Set.indicator_of_mem (show _ ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hiff.2 hx),
        Set.indicator_of_mem (show x ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hx)]
      rfl
    · rw [Set.indicator_of_notMem (show _ ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from mt hiff.1 hx),
        Set.indicator_of_notMem (show x ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hx)]
  · intro f φ _ _
    funext x
    simp only [LinearMap.funLeft_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
      Function.comp_apply]
    congr 1
    · congr 1
      funext i
      exact hom_mulVec evIr (algebraMap F (AF F)) gI rfl A⁻¹ x i
    · refine finprod_congr fun v => congrArg (φ v) ?_
      funext i
      exact hom_mulVec (evFin F v).toRingHom (algebraMap F (AF F)) (algebraMap F (Fv F v))
        (RingHom.ext fun c => (evFin F v).commutes c) A⁻¹ x i

end GlobalTheory.LeviOp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorForLeviMatrixStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_operator_for_levi_matrix : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → (∀ᶠ v in cofinite, PsiUnr ψ v) →
    (∀ v : Pl (F := F), ∃ x, psiLoc ψ v x ≠ 1) → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (A : Matrix κ κ F), IsUnit A.det →
    GlobalTheory.SympChange.HasOp ψ (GlobalTheory.SympChange.leviM A) := by
  first | exact @GlobalTheory.LeviOp.hasOp_levi | exact GlobalTheory.LeviOp.hasOp_levi | (intros; apply GlobalTheory.LeviOp.hasOp_levi <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumInnerIntegralEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvConjTMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalDegreeSumXMulCLe
namespace GlobalTheory.TotalDegreeBounds

open MvPolynomial

theorem totalDegree_aeval_le {σ τ R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (f : σ → MvPolynomial τ A) (hf : ∀ i, (f i).totalDegree ≤ 1) (P : MvPolynomial σ R) :
    (MvPolynomial.aeval f P).totalDegree ≤ P.totalDegree := by
  classical
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun d hd => ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  have h0 : (algebraMap R (MvPolynomial τ A) (AddMonoidAlgebra.coeff P d)).totalDegree = 0 := by
    rw [MvPolynomial.algebraMap_apply, MvPolynomial.totalDegree_C]
  rw [h0, zero_add]
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  refine le_trans ?_ (MvPolynomial.le_totalDegree hd)
  unfold Finsupp.sum
  refine Finset.sum_le_sum fun i _ => ?_
  refine (MvPolynomial.totalDegree_pow _ _).trans ?_
  simpa using Nat.mul_le_mul_left (d i) (hf i)

theorem totalDegree_sum_X_mul_C_le {ι τ A : Type*} [Fintype ι] [CommSemiring A]
    (g : ι → τ) (a : ι → A) :
    (∑ l : ι, (X (g l) * C (a l) : MvPolynomial τ A)).totalDegree ≤ 1 := by
  classical
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun l _ => ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, add_zero]
  refine (MvPolynomial.totalDegree_monomial_le _ _).trans ?_
  simp

theorem main : (let d1 : (n : ℕ) → Fin n × Fin n ⊕ Fin n × Fin n → MvPolynomial (Fin n × Fin n ⊕ Fin n × Fin n) (GlobalTheory.PsCo.Pc1.Poly n) := @(fun (n : ℕ) (x : Fin n × Fin n ⊕ Fin n × Fin n) ↦ match x with | Sum.inl x => ∑ l : Fin n, MvPolynomial.X (Sum.inr (l, Prod.fst x)) * (MvPolynomial.C : MvPolynomial (Fin n × Fin n ⊕ Fin n × Fin n) ℂ → MvPolynomial (Fin n × Fin n ⊕ Fin n × Fin n) (MvPolynomial (Fin n × Fin n ⊕ Fin n × Fin n) ℂ)) (MvPolynomial.X (Sum.inl (l, Prod.snd x))) | Sum.inr x => ∑ l : Fin n, MvPolynomial.X (Sum.inl (l, Prod.fst x)) * (MvPolynomial.C : MvPolynomial (Fin n × Fin n ⊕ Fin n × Fin n) ℂ → MvPolynomial (Fin n × Fin n ⊕ Fin n × Fin n) (MvPolynomial (Fin n × Fin n ⊕ Fin n × Fin n) ℂ)) (MvPolynomial.X (Sum.inr (l, Prod.snd x)))); let d2 : (n : ℕ) → GlobalTheory.PsCo.Pc1.Poly n →ₐ[ℂ] MvPolynomial (Fin n × Fin n ⊕ Fin n × Fin n) (GlobalTheory.PsCo.Pc1.Poly n) := @(fun (n : ℕ) ↦ MvPolynomial.aeval (d1 n)); ∀ {n : ℕ} (P : GlobalTheory.PsCo.Pc1.Poly n), MvPolynomial.totalDegree ((d2 n : GlobalTheory.PsCo.Pc1.Poly n → MvPolynomial (Fin n × Fin n ⊕ Fin n × Fin n) (GlobalTheory.PsCo.Pc1.Poly n)) P) ≤ MvPolynomial.totalDegree P) := by
  intro d1 d2 n P
  refine totalDegree_aeval_le (d1 n) ?_ P
  rintro (x | x)
  · exact totalDegree_sum_X_mul_C_le _ _
  · exact totalDegree_sum_X_mul_C_le _ _

end GlobalTheory.TotalDegreeBounds
end

noncomputable section

open MeasureTheory MvPolynomial
open Formalism.REAL (UJ KG toM toMK muK)
open GlobalTheory.PsCo.Pc1
open scoped InnerProductSpace

namespace GlobalTheory.PsCo.Pc3.RK

def linT (n : ℕ) : (Fin n × Fin n) ⊕ (Fin n × Fin n) → MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) (Poly n)
  | Sum.inl x => ∑ l, X (Sum.inr (l, x.1)) * C (X (Sum.inl (l, x.2)))
  | Sum.inr x => ∑ l, X (Sum.inl (l, x.1)) * C (X (Sum.inr (l, x.2)))

def TT (n : ℕ) : Poly n →ₐ[ℂ] MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) (Poly n) := aeval (linT n)

theorem TT_deg {n : ℕ} (P : Poly n) : (TT n P).totalDegree ≤ P.totalDegree := by
  first
  | exact @_root_.GlobalTheory.TotalDegreeBounds.main
  | exact _root_.GlobalTheory.TotalDegreeBounds.main
  | (apply _root_.GlobalTheory.TotalDegreeBounds.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.TotalDegreeBounds.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TotalDegreeBounds.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TotalDegreeBounds.main ..)

theorem ev_conjT_mul {n : ℕ} (A M : Mat n) (P : Poly n) :
    ev (A.conjTranspose * M) P =
      eval (Sum.elim (fun x => A x.1 x.2) (fun x => star (A x.1 x.2))) (map (ev M) (TT n P)) := by
  have h : (ev (A.conjTranspose * M) : Poly n →+* ℂ) =
      (eval (Sum.elim (fun x => A x.1 x.2) (fun x => star (A x.1 x.2)))).comp
        ((map (ev M)).comp (TT n).toRingHom) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun v => ?_)
    · simp [ev, TT, MvPolynomial.algebraMap_eq]
    · rcases v with x | x
      · simp [ev, TT, linT, Matrix.mul_apply]
      · simp [ev, TT, linT, Matrix.mul_apply]
  exact congrArg (fun f : Poly n →+* ℂ => f P) h

theorem eval_map_eq {n : ℕ} (x : (Fin n × Fin n) ⊕ (Fin n × Fin n) → ℂ) (f : Poly n →+* ℂ)
    (p : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) (Poly n)) :
    eval x (map f p) = ∑ s ∈ p.support, f (AddMonoidAlgebra.coeff p s) * eval x (monomial s 1) := by
  conv_lhs => rw [p.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_monomial, eval_monomial, one_mul]

end GlobalTheory.PsCo.Pc3.RK

namespace GlobalTheory.PsCo.Pc3

open RK

theorem rangeK : RangeK := by
  classical
  intro n ε U _ _ _ π hπ P
  have hemb : Topology.IsEmbedding (fun k : KG ε => toMK k) :=
    (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  have hφc : Continuous fun k : KG ε => toMK k := hemb.continuous
  have hevc : ∀ Q : Poly n, Continuous fun k : KG ε => ev (toMK k) Q := by
    intro Q
    have hent : Continuous fun k : KG ε =>
        (Sum.elim (fun x => toMK k x.1 x.2) (fun x => star (toMK k x.1 x.2)) :
          (Fin n × Fin n) ⊕ (Fin n × Fin n) → ℂ) := by
      refine continuous_pi fun i => ?_
      rcases i with x | x
      · exact (continuous_apply x.2).comp ((continuous_apply x.1).comp hφc)
      · exact continuous_star.comp ((continuous_apply x.2).comp ((continuous_apply x.1).comp hφc))
    exact (MvPolynomial.continuous_eval Q).comp hent
  have horb : ∀ v : U, Continuous fun k : KG ε => π k v :=
    fun v => (hπ.continuous_apply v).comp continuous_subtype_val
  have hint : ∀ (Q : Poly n) (v : U), Integrable (fun k : KG ε => ev (toMK k) Q • π k v) (muK ε) :=
    fun Q v => ((hevc Q).smul (horb v)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hintC : ∀ g : KG ε → ℂ, Continuous g → Integrable g (muK ε) :=
    fun g hg => hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  obtain ⟨M, hM⟩ := (isCompact_univ.image (hevc P)).isBounded.exists_norm_le
  have hMb : ∀ k : KG ε, ‖ev (toMK k) P‖ ≤ M := fun k => hM _ ⟨k, Set.mem_univ _, rfl⟩
  let Bl : U →ₗ[ℂ] U :=
    { toFun := fun v => ∫ k, ev (toMK k) P • π k v ∂(muK ε)
      map_add' := fun v w => by
        simp only [map_add (f := _), smul_add]
        exact integral_add (hint P v) (hint P w)
      map_smul' := fun c v => by
        simp only [map_smul, RingHom.id_apply]
        rw [← integral_smul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun k => smul_comm _ _ _) }
  let B : U →L[ℂ] U := Bl.mkContinuous (M * ((muK ε) Set.univ).toReal) fun v => by
    change ‖∫ k, ev (toMK k) P • π k v ∂(muK ε)‖ ≤ _
    have := norm_integral_le_of_norm_le_const (μ := muK ε) (C := M * ‖v‖)
      (f := fun k : KG ε => ev (toMK k) P • π k v) (Filter.Eventually.of_forall fun k => by
        rw [norm_smul, hπ.norm_apply]
        exact mul_le_mul_of_nonneg_right (hMb k) (norm_nonneg v))
    calc _ ≤ M * ‖v‖ * ((muK ε) Set.univ).toReal := this
      _ = M * ((muK ε) Set.univ).toReal * ‖v‖ := by ring
  refine ⟨B, fun v => ⟨hint P v, rfl⟩, fun u l => ?_⟩
  set p := TT n P with hp
  let f : KG ε → ℂ := fun k => ⟪l, π k u⟫_ℂ
  have hfc : Continuous f := continuous_const.inner (horb u)
  let c : _ → ℂ := fun s => ∫ k, ev (toMK k) (AddMonoidAlgebra.coeff p s) * f k ∂(muK ε)
  refine ⟨∑ s ∈ p.support, C (c s) * monomial s 1, ?_, fun k₀ => ?_⟩
  · refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun s hs => ?_)
    rw [C_mul_monomial, mul_one]
    exact (totalDegree_monomial_le _ _).trans ((le_totalDegree hs).trans (TT_deg P))
  · have hginv : toMK k₀⁻¹ = star (toMK k₀) := by
      have h1 : toMK k₀ * star (toMK k₀) = 1 := Unitary.mul_star_self_of_mem k₀.2.1
      calc toMK k₀⁻¹ = toMK k₀⁻¹ * (toMK k₀ * star (toMK k₀)) := by rw [h1, Matrix.mul_one]
        _ = star (toMK k₀) := by
          rw [← Matrix.mul_assoc]
          change toMK (k₀⁻¹ * k₀) * _ = _
          rw [inv_mul_cancel]
          exact Matrix.one_mul _
    have e1 : π k₀ (B u) = ∫ k, ev (toMK (k₀⁻¹ * k)) P • π k u ∂(muK ε) := by
      change π k₀ (∫ k, ev (toMK k) P • π k u ∂(muK ε)) = _
      rw [← (π k₀).integral_comp_comm (hint P u)]
      have e2 : ∫ k, π k₀ (ev (toMK k) P • π k u) ∂(muK ε) =
          ∫ k, (fun k' : KG ε => ev (toMK (k₀⁻¹ * k')) P • π (k' : UJ ε) u) (k₀ * k) ∂(muK ε) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
        simp only [map_smul, inv_mul_cancel_left, Subgroup.coe_mul, map_mul, ContinuousLinearMap.mul_apply]
      rw [e2, integral_mul_left_eq_self (fun k' : KG ε => ev (toMK (k₀⁻¹ * k')) P • π (k' : UJ ε) u) k₀]
    have hexp : ∀ k : KG ε, ev (toMK (k₀⁻¹ * k)) P =
        ∑ s ∈ p.support, ev (toMK k) (AddMonoidAlgebra.coeff p s) * ev (toMK k₀) (monomial s 1) := by
      intro k
      change ev (toMK k₀⁻¹ * toMK k) P = _
      rw [hginv, show star (toMK k₀) = (toMK k₀).conjTranspose from rfl, ev_conjT_mul, eval_map_eq]
      rfl
    have hint2 : ∀ s, Integrable (fun k : KG ε => ev (toMK k) (AddMonoidAlgebra.coeff p s) * f k) (muK ε) :=
      fun s => hintC _ ((hevc _).mul hfc)
    have hint3 : Integrable (fun k : KG ε => ev (toMK (k₀⁻¹ * k)) P • π k u) (muK ε) :=
      (((hevc P).comp (continuous_const.mul continuous_id)).smul (horb u)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    calc ⟪l, π k₀ (B u)⟫_ℂ = ∫ k, ⟪l, ev (toMK (k₀⁻¹ * k)) P • π k u⟫_ℂ ∂(muK ε) := by
          rw [e1, integral_inner hint3]
      _ = ∫ k, ∑ s ∈ p.support, ev (toMK k₀) (monomial s 1) * (ev (toMK k) (AddMonoidAlgebra.coeff p s) * f k) ∂(muK ε) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
          simp only [inner_smul_right, hexp k, Finset.sum_mul]
          refine Finset.sum_congr rfl fun s _ => ?_
          ring
      _ = ∑ s ∈ p.support, ev (toMK k₀) (monomial s 1) * c s := by
          rw [integral_finsetSum _ fun s _ => (hint2 s).const_mul _]
          exact Finset.sum_congr rfl fun s _ => integral_const_mul _ _
      _ = ev (toMK k₀) (∑ s ∈ p.support, C (c s) * monomial s 1) := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [map_sum, map_mul, ev, eval_C]
          exact Finset.sum_congr rfl fun s _ => mul_comm _ _

end GlobalTheory.PsCo.Pc3
end
end

noncomputable section

open MeasureTheory GlobalTheory.Orb GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open Formalism.REAL (UJ KG toM toMK muK)
open GlobalTheory.PsCo.Pc1
open scoped InnerProductSpace

namespace GlobalTheory.PsCo.Pc3

theorem sum_inner_integral_eq {X U ι : Type} [MeasurableSpace X] [NormedAddCommGroup U] [InnerProductSpace ℂ U]
    [CompleteSpace U] [Fintype ι] (ν : Measure X) (f : X → ℂ) (ρ : X → U →L[ℂ] U) (e : ι → U) (T : U →L[ℂ] U)
    (h : ∀ v, Integrable (fun x => f x • ρ x v) ν ∧ T v = ∫ x, f x • ρ x v ∂ν) :
    ∑ j, ⟪e j, T (e j)⟫_ℂ = ∫ x, f x * ∑ j, ⟪e j, ρ x (e j)⟫_ℂ ∂ν := by
  have h1 : ∀ j, ⟪e j, T (e j)⟫_ℂ = ∫ x, ⟪e j, f x • ρ x (e j)⟫_ℂ ∂ν := fun j => by
    rw [(h (e j)).2, integral_inner (h (e j)).1]
  simp only [h1]
  rw [← integral_finsetSum _ fun j _ => (h (e j)).1.const_inner (e j)]
  simp only [inner_smul_right, Finset.mul_sum]

theorem stTr_of_range_steps (hF : UFin) (hS : RangeShape) (hK : RangeK) (hT : TraceSum) : StTr := by
  intro n ε μ _ U _ _ _ π hπ hirr d
  obtain ⟨L, hL, hmem, -⟩ := hF n ε U π hπ hirr d
  refine ⟨fun g => ∑ j, ⟪(stdOrthonormalBasis ℂ L j : U), π g (stdOrthonormalBasis ℂ L j : U)⟫_ℂ, ?_, ?_, ?_⟩
  · exact continuous_finsetSum _ fun j _ => continuous_const.inner (hπ.continuous_apply _)
  · intro φ hφ
    obtain ⟨hop, hr⟩ := hS n ε μ U π hπ d φ hφ
    have := hT U L _ fun u => hmem _ (hr u).1
    rwa [sum_inner_integral_eq μ (fun g => φ (toM g)) (fun g => π g) _ _ hop] at this
  · intro P hP
    obtain ⟨B, hB, hr⟩ := hK n ε U π hπ P
    refine ⟨B, fun v => (hB v).2, ?_⟩
    have := hT U L B fun u => hmem _ fun l => by
      obtain ⟨Q, hQ, hQ'⟩ := hr u l
      exact ⟨Q, hQ.trans hP, hQ'⟩
    rwa [sum_inner_integral_eq (muK ε) (fun k : KG ε => ev (toMK k) P) (fun k : KG ε => π k) _ _ hB] at this

theorem stTr : StTr := stTr_of_range_steps GlobalTheory.T.polyCoeff_vectors_lie_in_finiteDimensional_smooth GlobalTheory.T.shapeIntegratedOperator_ranges_polynomial rangeK GlobalTheory.OpTrace.hasTrace_sum_inner_of_range_le

end GlobalTheory.PsCo.Pc3

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalHermitianForm
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RefForm

theorem cT_mul {A : Type} [CommRing A] (σ : A →+* A) {k : ℕ} (X Y : Matrix (Fin k) (Fin k) A) :
    cT σ (X * Y) = cT σ Y * cT σ X := by
  simp [cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_cT_conj {k : ℕ} (X : Matrix (Fin k) (Fin k) ℂ) : cT (starRingEnd ℂ) (cT (starRingEnd ℂ) X) = X := by
  ext i j; simp [cT]

theorem det_cT_conj {k : ℕ} (X : Matrix (Fin k) (Fin k) ℂ) : (cT (starRingEnd ℂ) X).det = starRingEnd ℂ X.det := by
  simp only [cT, Matrix.det_transpose]
  exact ((starRingEnd ℂ).map_det X).symm

theorem cT_diag_mul_diag {k : ℕ} (μ : Fin k → ℂ) (hμ : ∀ r, ‖μ r‖ = 1) :
    cT (starRingEnd ℂ) (Matrix.diagonal μ) * Matrix.diagonal μ = 1 := by
  have : cT (starRingEnd ℂ) (Matrix.diagonal μ) = Matrix.diagonal (fun r => starRingEnd ℂ (μ r)) := by
    ext i j; by_cases h : i = j
    · subst h; simp [cT]
    · simp [cT, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]
  rw [this, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext r
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hμ r]; simp

theorem assemble (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (γ H : Matrix (Fin n) (Fin n) E)
    (h : ∀ τ : E →+* ℂ, ∃ (W : Matrix (Fin n) (Fin n) ℂ) (μ : Fin n → ℂ), W.det ≠ 0 ∧ (∀ r, ‖μ r‖ = 1) ∧
      W * γ.map τ = Matrix.diagonal μ * W ∧ H.map τ = cT (starRingEnd ℂ) W * W) :
    IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H ∧ H.det ≠ 0 ∧
      cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ * H * γ = H ∧
      (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H.map τ = cT (starRingEnd ℂ) Q * Q) := by
  set σ := (IsCMField.complexConj E).toRingEquiv.toRingHom
  have hστ : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = starRingEnd ℂ (τ x) := fun τ x =>
    IsCMField.complexEmbedding_complexConj E τ x
  have hmapcT : ∀ (τ : E →+* ℂ) (X : Matrix (Fin n) (Fin n) E),
      (cT σ X).map τ = cT (starRingEnd ℂ) (X.map τ) := by
    intro τ X; ext i j; simp [cT, hστ]
  obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hinj : Function.Injective (fun X : Matrix (Fin n) (Fin n) E => X.map τ₀) :=
    Matrix.map_injective τ₀.injective
  obtain ⟨W, μ, hW, hμ, hWγ, hH⟩ := h τ₀
  refine ⟨?_, ?_, ?_, fun τ => ?_⟩
  · apply hinj
    change (cT σ H).map τ₀ = H.map τ₀
    rw [hmapcT, hH, cT_mul, cT_cT_conj]
  · intro h0
    have : τ₀ H.det = 0 := by rw [h0, map_zero]
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hH, Matrix.det_mul, det_cT_conj] at this
    rcases mul_eq_zero.mp this with h1 | h1
    · exact hW (by simpa using h1)
    · exact hW h1
  · apply hinj
    change (cT σ γ * H * γ).map τ₀ = H.map τ₀
    rw [Matrix.map_mul, Matrix.map_mul, hmapcT, hH]
    calc cT (starRingEnd ℂ) (γ.map τ₀) * (cT (starRingEnd ℂ) W * W) * γ.map τ₀
        = cT (starRingEnd ℂ) (W * γ.map τ₀) * (W * γ.map τ₀) := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = cT (starRingEnd ℂ) W * (cT (starRingEnd ℂ) (Matrix.diagonal μ) * Matrix.diagonal μ) * W := by
          rw [hWγ, cT_mul]; simp only [Matrix.mul_assoc]
      _ = cT (starRingEnd ℂ) W * W := by rw [cT_diag_mul_diag μ hμ, Matrix.mul_one]
  · obtain ⟨W, μ, hW, -, -, hH⟩ := h τ
    exact ⟨W, hW, hH⟩

end GlobalTheory.RefForm

namespace GlobalTheory.RefForm

theorem exists_roots_enum (E : Type) [Field E] (n : ℕ) (P : E[X]) (hP : P ∈ Ell E n) (τ : E →+* ℂ) :
    ∃ μ : Fin n → ℂ, Function.Injective μ ∧ (∀ r, ‖μ r‖ = 1) ∧ ∀ r, P.eval₂ τ (μ r) = 0 := by
  obtain ⟨hm, hn, hs, hr⟩ := hP
  set s := (P.map τ).roots
  have hnd : s.Nodup := nodup_roots (hs.map)
  have hcard : s.card = n := by
    rw [← hn, ← Polynomial.natDegree_map τ]
    exact splits_iff_card_roots.mp (IsAlgClosed.splits _)
  have hc : s.toFinset.card = n := by rw [Multiset.toFinset_card_of_nodup hnd, hcard]
  let e : Fin n ≃ s.toFinset := (finCongr hc.symm).trans s.toFinset.equivFin.symm
  refine ⟨fun r => ((e r) : ℂ), Subtype.val_injective.comp e.injective, fun r => hr τ _ ?_, fun r => ?_⟩
  · exact Multiset.mem_toFinset.mp (e r).2
  · have hmem : ((e r) : ℂ) ∈ s := Multiset.mem_toFinset.mp (e r).2
    rw [← Polynomial.eval_map]
    exact (mem_roots (hm.map τ).ne_zero).mp hmem

noncomputable def powBasis {E : Type} [Field E] (P : E[X]) (hm : P.Monic) :
    Module.Basis (Fin P.natDegree) E (AdjoinRoot P) :=
  (AdjoinRoot.powerBasis hm.ne_zero).basis.reindex (finCongr (AdjoinRoot.powerBasis_dim hm.ne_zero))

theorem powBasis_apply {E : Type} [Field E] (P : E[X]) (hm : P.Monic) (i : Fin P.natDegree) :
    powBasis P hm i = AdjoinRoot.root P ^ (i : ℕ) := by
  simp [powBasis, Module.Basis.reindex_apply, PowerBasis.coe_basis, AdjoinRoot.powerBasis_gen]

noncomputable def compMat {E : Type} [Field E] (P : E[X]) (hm : P.Monic) :
    Matrix (Fin P.natDegree) (Fin P.natDegree) E :=
  Algebra.leftMulMatrix (powBasis P hm) (AdjoinRoot.root P)

theorem vandermonde_mul_compMat (E : Type) [Field E] (P : E[X]) (hm : P.Monic) (τ : E →+* ℂ)
    (μ : Fin P.natDegree → ℂ) (hμ : ∀ r, P.eval₂ τ (μ r) = 0) :
    Matrix.vandermonde μ * (compMat P hm).map τ = Matrix.diagonal μ * Matrix.vandermonde μ := by
  ext r j
  let φ : AdjoinRoot P →+* ℂ := AdjoinRoot.lift τ (μ r) (hμ r)
  have hφ : ∀ a : AdjoinRoot P, φ a = ∑ i, τ ((powBasis P hm).repr a i) * μ r ^ (i : ℕ) := by
    intro a
    conv_lhs => rw [← (powBasis P hm).sum_repr a]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, map_mul, powBasis_apply, map_pow]
    simp [φ, AdjoinRoot.lift_root, AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of]
  have key := hφ (AdjoinRoot.root P * powBasis P hm j)
  rw [map_mul, powBasis_apply, map_pow] at key
  simp only [φ, AdjoinRoot.lift_root] at key
  rw [Matrix.diagonal_mul]
  simp only [Matrix.mul_apply, Matrix.vandermonde_apply, Matrix.map_apply,
    compMat, Algebra.leftMulMatrix_eq_repr_mul, powBasis_apply]
  rw [key]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem charpoly_compMat {E : Type} [Field E] (P : E[X]) (hm : P.Monic) : (compMat P hm).charpoly = P := by
  haveI : Module.Finite E (AdjoinRoot P) := Module.Finite.of_basis (powBasis P hm)
  have h1 : (compMat P hm).charpoly = (Algebra.lmul E (AdjoinRoot P) (AdjoinRoot.root P)).charpoly :=
    LinearMap.charpoly_toMatrix _ _
  have h2 : (Algebra.leftMulMatrix (AdjoinRoot.powerBasis hm.ne_zero).basis (AdjoinRoot.root P)).charpoly =
      (Algebra.lmul E (AdjoinRoot P) (AdjoinRoot.root P)).charpoly :=
    LinearMap.charpoly_toMatrix _ _
  rw [h1, ← h2]
  have := (charpoly_leftMulMatrix (AdjoinRoot.powerBasis hm.ne_zero)).trans
      (AdjoinRoot.minpoly_powerBasis_gen_of_monic hm)
  simpa [AdjoinRoot.powerBasis_gen] using this

end GlobalTheory.RefForm

namespace GlobalTheory.RefForm

theorem trace_semiconj {k : ℕ} (W T T' : Matrix (Fin k) (Fin k) ℂ) (μ : Fin k → ℂ) (hμ0 : ∀ r, μ r ≠ 0)
    (hW : W.det ≠ 0) (hWT : W * T = Matrix.diagonal μ * W) (hTT' : T * T' = 1) (i j : ℕ) :
    (T' ^ i * T ^ j).trace = ∑ r, (μ r)⁻¹ ^ i * μ r ^ j := by
  have hinv : Matrix.diagonal (fun r => (μ r)⁻¹) * Matrix.diagonal μ = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext r; exact inv_mul_cancel₀ (hμ0 r)
  have hWT' : W * T' = Matrix.diagonal (fun r => (μ r)⁻¹) * W := by
    calc W * T' = Matrix.diagonal (fun r => (μ r)⁻¹) * Matrix.diagonal μ * W * T' := by
          rw [hinv, Matrix.one_mul]
      _ = Matrix.diagonal (fun r => (μ r)⁻¹) * (W * T) * T' := by
          rw [hWT, Matrix.mul_assoc (Matrix.diagonal _) (Matrix.diagonal μ) W]
      _ = Matrix.diagonal (fun r => (μ r)⁻¹) * W := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, hTT', Matrix.mul_one]
  have h1 : SemiconjBy W T' (Matrix.diagonal fun r => (μ r)⁻¹) := hWT'
  have h2 : SemiconjBy W T (Matrix.diagonal μ) := hWT
  have hs := (h1.pow_right i).mul_right (h2.pow_right j)
  rw [Matrix.diagonal_pow, Matrix.diagonal_pow, Matrix.diagonal_mul_diagonal] at hs
  have hu : IsUnit W.det := isUnit_iff_ne_zero.mpr hW
  have hM : T' ^ i * T ^ j = W⁻¹ * (Matrix.diagonal (fun r => ((fun r => (μ r)⁻¹) ^ i) r * (μ ^ j) r) * W) := by
    rw [← hs.eq, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
  rw [hM, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one,
    Matrix.trace_diagonal]
  simp

theorem exists_model (E : Type) [Field E] [NumberField E] (n : ℕ) (P : E[X]) (hP : P ∈ Ell E n) :
    ∃ (N : GL (Fin n) E) (H : Matrix (Fin n) (Fin n) E), N.val.charpoly = P ∧
      ∀ τ : E →+* ℂ, ∃ (W : Matrix (Fin n) (Fin n) ℂ) (μ : Fin n → ℂ), W.det ≠ 0 ∧ (∀ r, ‖μ r‖ = 1) ∧
        W * N.val.map τ = Matrix.diagonal μ * W ∧ H.map τ = cT (starRingEnd ℂ) W * W := by
  have hP' := hP
  obtain ⟨hm, hn, -, hr⟩ := hP
  subst hn
  have h0 : P.coeff 0 ≠ 0 := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    intro h
    have hroot : (0 : ℂ) ∈ (P.map τ).roots := by
      rw [mem_roots (hm.map τ).ne_zero, IsRoot.def, ← coeff_zero_eq_eval_zero, coeff_map, h, map_zero]
    have := hr τ 0 hroot
    simp at this
  have hd : IsUnit (compMat P hm).det := by
    rw [Matrix.det_eq_sign_charpoly_coeff, charpoly_compMat]
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) h0)
  set N : GL (Fin P.natDegree) E := ((Matrix.isUnit_iff_isUnit_det _).mpr hd).unit with hNdef
  have hNval : N.val = compMat P hm := IsUnit.unit_spec _
  refine ⟨N, Matrix.of fun i j => ((N⁻¹).val ^ (i : ℕ) * N.val ^ (j : ℕ)).trace, by rw [hNval, charpoly_compMat],
    fun τ => ?_⟩
  obtain ⟨μ, hμi, hμ1, hμr⟩ := exists_roots_enum E _ P hP' τ
  have hμ0 : ∀ r, μ r ≠ 0 := fun r h => by simpa [h] using hμ1 r
  have hW : (Matrix.vandermonde μ).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hμi
  have hWT : Matrix.vandermonde μ * N.val.map τ = Matrix.diagonal μ * Matrix.vandermonde μ := by
    rw [hNval]; exact vandermonde_mul_compMat E P hm τ μ hμr
  have hTT' : N.val.map τ * (N⁻¹).val.map τ = 1 := by
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero τ) (map_one τ)]
  refine ⟨Matrix.vandermonde μ, μ, hW, hμ1, hWT, ?_⟩
  ext i j
  rw [Matrix.map_apply, Matrix.of_apply, AddMonoidHom.map_trace τ]
  have hmap : (((N⁻¹).val ^ (i : ℕ) * N.val ^ (j : ℕ)).map τ) =
      ((N⁻¹).val.map τ) ^ (i : ℕ) * (N.val.map τ) ^ (j : ℕ) := by
    simp only [← RingHom.mapMatrix_apply, map_mul, map_pow]
  rw [hmap, trace_semiconj _ _ _ μ hμ0 hW hWT hTT']
  simp only [cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.vandermonde_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [map_pow, Complex.inv_eq_conj (hμ1 r)]

end GlobalTheory.RefForm

namespace GlobalTheory.RefForm

theorem map_cT_complexConj (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (τ : E →+* ℂ)
    (X : Matrix (Fin n) (Fin n) E) :
    (cT (IsCMField.complexConj E).toRingEquiv.toRingHom X).map τ = cT (starRingEnd ℂ) (X.map τ) := by
  ext i j; simp [cT, IsCMField.complexEmbedding_complexConj E τ]

theorem exists_refForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ₀ : GL (Fin n) E),
    γ₀.val.charpoly ∈ Ell E n → ∃ H₀ : Matrix (Fin n) (Fin n) E,
      IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ ∧ H₀.det ≠ 0 ∧
      cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ ∧
      (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H₀.map τ = cT (starRingEnd ℂ) Q * Q) := by
  intro E _ _ _ n γ₀ hP
  obtain ⟨N, H, hNc, hmod⟩ := exists_model E n _ hP
  obtain ⟨h, hh⟩ := GlobalTheory.SepConj.conj_of_charpoly_eq_of_separable E n N γ₀ hNc (hNc ▸ hP.2.2.1)
  refine ⟨cT (IsCMField.complexConj E).toRingEquiv.toRingHom h.val * H * h.val,
    assemble E n γ₀.val _ fun τ => ?_⟩
  obtain ⟨W, μ, hW, hμ1, hWN, hH⟩ := hmod τ
  have hinv1 : h.val.map τ * (h⁻¹).val.map τ = 1 := by
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero τ) (map_one τ)]
  have hdh : (h.val.map τ).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hinv1
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  refine ⟨W * h.val.map τ, μ, by rw [Matrix.det_mul]; exact mul_ne_zero hW hdh, hμ1, ?_, ?_⟩
  · rw [hh, Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul]
    calc W * h.val.map τ * ((h⁻¹).val.map τ * N.val.map τ * h.val.map τ)
        = W * (h.val.map τ * (h⁻¹).val.map τ) * N.val.map τ * h.val.map τ := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal μ * (W * h.val.map τ) := by
          rw [hinv1, Matrix.mul_one, hWN, Matrix.mul_assoc]
  · rw [Matrix.map_mul, Matrix.map_mul, map_cT_complexConj, hH, cT_mul]
    simp only [Matrix.mul_assoc]

end GlobalTheory.RefForm
end
