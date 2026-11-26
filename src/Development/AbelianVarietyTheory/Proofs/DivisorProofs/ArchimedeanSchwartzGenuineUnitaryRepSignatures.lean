module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftDarbouxAdelicSymplectic
public import CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.RealMetaplecticRepresentationHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerCongruentOfCommutatorPhaseEq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousHomUnitaryRealPlacesPlacewiseSig
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousHomUnitaryRealPlacesPlacewiseSig
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix RealInnerProductSpace
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical
open GlobalTheory.HoweD

noncomputable section

namespace GlobalTheory.RealLiftCompD

open Matrix GlobalTheory.RealLiftGen

theorem exists_compD : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (β : Type) [Fintype β]
    [DecidableEq β] (R S : InfinitePlace F → ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (AE F E)) (b : ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ), IsCMExt F E σ → (∀ w, IsFrame (b • J.map (piInf (τ w))) (C w)) →
    ∃ k : UG (cA σ) J →* (∀ w : InfinitePlace F, Mat (R w) (S w)), Continuous k ∧
      (∀ g w, (g.1 : Matrix β β (AE F E)).map (piInf (τ w)) * C w = C w * k g w) ∧
      (∀ g w, (k g w)ᴴ * Jm (R w) (S w) * k g w = Jm (R w) (S w)) ∧ ∀ w (M M' : Mat (R w) (S w)), C w * M = C w * M' → M = M' := by
  intro F E _ _ _ _ _ σ β _ _ R S τ J b C hcm hC
  choose A' hA' using fun w => (hC w).2
  set K : InfinitePlace F → Matrix β β ℂ := fun w => b • J.map (piInf (τ w)) with hK
  have hF : ∀ w, (C w)ᵀ * K w * (C w).map star = Jm (R w) (S w) := fun w => (hC w).1
  have hAC : ∀ w, A' w * C w = 1 := by
    intro w
    have h1 : (Jm (R w) (S w) * (C w)ᵀ * K w) * (C w).map star = 1 := by
      rw [Matrix.mul_assoc (Jm (R w) (S w)), Matrix.mul_assoc (Jm (R w) (S w)), hF, Jm_mul_Jm]
    have h2 : (Jm (R w) (S w) * (C w)ᵀ * K w).map star * C w = 1 := by
      have := congrArg (fun X => X.map star) h1
      rw [map_star_mul, map_star_star] at this
      rw [this]; ext i j; simp [Matrix.one_apply]
    calc A' w * C w = ((Jm (R w) (S w) * (C w)ᵀ * K w).map star * C w) * A' w * C w := by rw [h2, Matrix.one_mul]
      _ = (Jm (R w) (S w) * (C w)ᵀ * K w).map star * C w := by rw [Matrix.mul_assoc _ (C w), hA', Matrix.mul_one]
      _ = 1 := h2
  set M : UG (cA σ) J → InfinitePlace F → Matrix β β ℂ :=
    fun g w => (g.1 : Matrix β β (AE F E)).map (piInf (τ w)) with hM
  have hMmul : ∀ g h w, M (g * h) w = M g w * M h w := by
    intro g h w
    simp only [hM, Subgroup.coe_mul, Units.val_mul]
    exact Matrix.map_mul
  have hM1 : ∀ w, M 1 w = 1 := by
    intro w
    simp only [hM, OneMemClass.coe_one, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hMu : ∀ g w, (M g w)ᵀ * K w * (M g w).map star = K w := by
    intro g w
    have hg := g.2
    change ((g.1 : Matrix β β (AE F E)))ᵀ * J * ((g.1 : Matrix β β (AE F E))).map (cA σ) = J at hg
    have h2 := congrArg (fun X => X.map (piInf (τ w))) hg
    simp only [Matrix.map_mul, Matrix.map_map] at h2
    have h3 : (piInf (τ w)) ∘ (cA σ) = star ∘ (piInf (τ w)) := funext fun x => piInf_cA hcm (τ w) x
    rw [h3, ← Matrix.map_map] at h2
    have h4 : (M g w)ᵀ * J.map (piInf (τ w)) * (M g w).map star = J.map (piInf (τ w)) := by
      simp only [hM]; rw [← Matrix.transpose_map]; exact h2
    simp only [hK, Matrix.mul_smul, Matrix.smul_mul]
    rw [h4]
  let k : UG (cA σ) J →* (∀ w : InfinitePlace F, Mat (R w) (S w)) :=
    { toFun := fun g w => A' w * M g w * C w
      map_one' := by funext w; simp only [hM1, Matrix.mul_one, hAC, Pi.one_apply]
      map_mul' := by
        intro g h; funext w
        simp only [hMmul, Pi.mul_apply]
        calc A' w * (M g w * M h w) * C w = A' w * M g w * (C w * A' w) * M h w * C w := by
              rw [hA', Matrix.mul_one]; simp only [Matrix.mul_assoc]
          _ = _ := by simp only [Matrix.mul_assoc] }
  have hk : ∀ g w, k g w = A' w * M g w * C w := fun _ _ => rfl
  have hCk : ∀ g w, C w * k g w = M g w * C w := by
    intro g w; simp only [hk, ← Matrix.mul_assoc, hA', Matrix.one_mul]
  refine ⟨k, ?_, fun g w => (hCk g w).symm, fun g w => ?_, fun w X X' h => ?_⟩
  · have h1 : Continuous (fun g : UG (cA σ) J => ((g.1 : Matrix β β (AE F E)))) :=
      Units.continuous_val.comp continuous_subtype_val
    refine continuous_pi fun w => ?_
    exact (continuous_const.matrix_mul (h1.matrix_map (GlobalTheory.ContMapReal.continuous_piInf (τ w)))).matrix_mul
      continuous_const
  · have hT : (k g w)ᵀ * Jm (R w) (S w) * (k g w).map star = Jm (R w) (S w) := by
      rw [← hF w]
      calc (k g w)ᵀ * ((C w)ᵀ * K w * (C w).map star) * (k g w).map star
          = (C w * k g w)ᵀ * K w * (C w * k g w).map star := by
            simp only [Matrix.transpose_mul, map_star_mul, Matrix.mul_assoc]
        _ = (C w)ᵀ * ((M g w)ᵀ * K w * (M g w).map star) * (C w).map star := by
            simp only [hCk, Matrix.transpose_mul, map_star_mul, Matrix.mul_assoc]
        _ = _ := by rw [hMu]
    have h2 := congrArg (fun X => X.map star) hT
    simp only [map_star_mul, Jm_map_star, map_star_star] at h2
    exact h2
  · have := congrArg (fun Y => A' w * Y) h
    simpa only [← Matrix.mul_assoc, hAC, Matrix.one_mul] using this

end GlobalTheory.RealLiftCompD
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousHomUnitaryRealPlacesPlacewiseSigStatement
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix RealInnerProductSpace
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical
open GlobalTheory.HoweD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_hom_unitary_realPlaces_placewise_signature : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (β : Type) [Fintype β]
    [DecidableEq β] (R S : InfinitePlace F → ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (b : ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ), IsCMExt F E σ → (∀ w, IsFrame (b • J.map (piInf (τ w))) (C w)) →
    ∃ k : UG (cA σ) J →* (∀ w : InfinitePlace F, Mat (R w) (S w)), Continuous k ∧
      (∀ g w, (g.1 : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))).map (piInf (τ w)) * C w = C w * k g w) ∧
      (∀ g w, (k g w)ᴴ * Jm (R w) (S w) * k g w = Jm (R w) (S w)) ∧ ∀ w (M M' : Mat (R w) (S w)), C w * M = C w * M' → M = M' := by
  first | exact @GlobalTheory.RealLiftCompD.exists_compD | exact GlobalTheory.RealLiftCompD.exists_compD | (intros; apply GlobalTheory.RealLiftCompD.exists_compD <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionQuadraticOperatorsFactorSignatures
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionQuadraticOperatorsFactorSignatures
open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil
open GlobalTheory.HoweD

noncomputable section

namespace GlobalTheory.HoweD.QuadFockD

open GlobalTheory.RealLift.QuadFock

variable {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ι → ℕ}

abbrev MD (P Q R S : ι → ℕ) (w : ι) : Type := Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ

theorem sumPl_singleD (w : ι) (M : MD P Q R S w) :
    sumPl (V := fun w => Pol (P w) (Q w) (R w) (S w))
      (fun w' => heisOp ((Pi.single w M : ∀ w', MD P Q R S w') w')) = atPl w (heisOp M) := by
  unfold sumPl
  rw [Finset.sum_eq_single w]
  · simp
  · intro b _ hb
    dsimp only
    rw [Pi.single_eq_of_ne hb, heisOp_zero, atPl_zero]
  · simp

def eS (w : ι) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) (x : ℂ) : ∀ w', MD P Q R S w' :=
  Pi.single w (Matrix.single a b x)

theorem eS_ne (w : ι) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) (x : ℂ) {w' : ι} (h : w' ≠ w) :
    eS w a b x w' = 0 := by
  simp [eS, Pi.single_eq_of_ne h]

theorem eS_same (w : ι) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) (x : ℂ) :
    eS w a b x w = Matrix.single a b x := by
  simp [eS]

theorem sum_eS (w : ι) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) (x : ℂ) (c : ∀ w', MD P Q R S w') :
    (∑ w', ∑ a', ∑ b', lineSign a' b' * eS w a b x w' a' b' * star (c w' a' b')) =
      lineSign a b * x * star (c w a b) := by
  rw [Finset.sum_eq_single w]
  · rw [eS_same, Finset.sum_eq_single a, Finset.sum_eq_single b]
    · simp [Matrix.single_apply]
    · intro y _ hy; simp [Matrix.single_apply, hy, Ne.symm hy]
    · simp
    · intro y _ hy
      refine Finset.sum_eq_zero fun b' _ => ?_
      simp [Matrix.single_apply, hy, Ne.symm hy]
    · simp
  · intro y _ hy
    simp [eS_ne w a b x hy]
  · simp

theorem decomp (c : ∀ w, MD P Q R S w) :
    c = ∑ w, ∑ a, ∑ b, ((c w a b).re • eS w a b 1 + (c w a b).im • eS w a b Complex.I) := by
  funext w
  ext a b
  simp only [Finset.sum_apply, Matrix.sum_apply, Pi.add_apply, Pi.smul_apply, Matrix.add_apply,
    Matrix.smul_apply]
  rw [Finset.sum_eq_single w]
  · simp only [eS_same]
    rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
    · simp only [Matrix.single_apply, and_self, if_true, Complex.real_smul, mul_one]
      exact (Complex.re_add_im _).symm
    · intro y _ hy; simp [Matrix.single_apply, hy, Ne.symm hy]
    · simp
    · intro y _ hy
      refine Finset.sum_eq_zero fun b' _ => ?_
      simp [Matrix.single_apply, hy, Ne.symm hy]
    · simp
  · intro y _ hy
    refine Finset.sum_eq_zero fun a' _ => Finset.sum_eq_zero fun b' _ => ?_
    simp [eS_ne _ _ _ _ (Ne.symm hy)]
  · simp

abbrev Idx (P Q R S : ι → ℕ) : Type := Σ w : ι, Ix (P w) (Q w) × Ix (R w) (S w) × Bool

def cu (i : Idx P Q R S) : ∀ w, MD P Q R S w :=
  if i.2.2.2 then (sgn i.2.1 i.2.2.1 / 2) • eS i.1 i.2.1 i.2.2.1 1
  else (-(sgn i.2.1 i.2.2.1 / 2)) • eS i.1 i.2.1 i.2.2.1 Complex.I

def cv (i : Idx P Q R S) : ∀ w, MD P Q R S w :=
  if i.2.2.2 then eS i.1 i.2.1 i.2.2.1 Complex.I else eS i.1 i.2.1 i.2.2.1 1

theorem sum_idx {M : Type} [AddCommMonoid M] (f : Idx P Q R S → M) :
    ∑ i, f i = ∑ w, ∑ a, ∑ b, (f ⟨w, a, b, true⟩ + f ⟨w, a, b, false⟩) := by
  rw [Fintype.sum_sigma]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]

theorem dual {l : Type} [Fintype l] (φ : (∀ w, MD P Q R S w) ≃ₗ[ℝ] (l ⊕ l → ℝ))
    (hφ : ∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im)
    (x : l ⊕ l → ℝ) : ∑ i, sympl (φ (cv i)) x • φ (cu i) = x := by
  obtain ⟨c, rfl⟩ := φ.surjective x
  have e1 : ∀ i, sympl (φ (cv i)) (φ c) • φ (cu i) = φ (sympl (φ (cv i)) (φ c) • cu i) :=
    fun i => (map_smul φ _ _).symm
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [e1, ← map_sum]
  congr 1
  conv_rhs => rw [decomp c]
  rw [sum_idx]
  simp only [cu, cv, if_true, Bool.false_eq_true, if_false, hφ, sum_eS]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [smul_smul, smul_smul, lineSign_eq_sgn]
  have h2 := sgn_mul_self a b
  congr 2
  · simp [Complex.mul_im, Complex.mul_re]
    linear_combination (c w a b).re * h2
  · simp [Complex.mul_im, Complex.mul_re]
    linear_combination (c w a b).im * h2

end GlobalTheory.HoweD.QuadFockD

namespace GlobalTheory.HoweD.QuadFockD

open GlobalTheory.RealLift.QuadFock

variable {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ι → ℕ}

theorem cu_true_mul (Y : ∀ w, Mat (R w) (S w)) (w : ι) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) (w' : ι) :
    cu (P := P) (Q := Q) ⟨w, a, b, true⟩ w' * (Y w')ᵀ =
      (Pi.single w ((sgn a b / 2) • (Matrix.single a b (1 : ℂ) * (Y w)ᵀ)) : ∀ w', MD P Q R S w') w' := by
  by_cases h : w' = w
  · subst h
    simp only [cu, eS, if_true, Pi.smul_apply, Pi.single_eq_same, Matrix.smul_mul]
  · simp [cu, eS, h]

theorem cu_false_mul (Y : ∀ w, Mat (R w) (S w)) (w : ι) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) (w' : ι) :
    cu (P := P) (Q := Q) ⟨w, a, b, false⟩ w' * (Y w')ᵀ =
      (Pi.single w ((-(sgn a b / 2)) • (Matrix.single a b Complex.I * (Y w)ᵀ)) : ∀ w', MD P Q R S w') w' := by
  by_cases h : w' = w
  · subst h
    simp only [cu, eS, Bool.false_eq_true, if_false, Pi.smul_apply, Pi.single_eq_same, Matrix.smul_mul]
  · simp [cu, eS, h]

theorem cv_true (w : ι) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) :
    cv (P := P) (Q := Q) (R := R) (S := S) ⟨w, a, b, true⟩ =
      (Pi.single w (Matrix.single a b Complex.I) : ∀ w', MD P Q R S w') := by
  simp [cv, eS]

theorem cv_false (w : ι) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) :
    cv (P := P) (Q := Q) (R := R) (S := S) ⟨w, a, b, false⟩ =
      (Pi.single w (Matrix.single a b (1 : ℂ)) : ∀ w', MD P Q R S w') := by
  simp [cv, eS]

end GlobalTheory.HoweD.QuadFockD

namespace GlobalTheory.HoweD

open GlobalTheory.RealLift.QuadFock GlobalTheory.HoweD.QuadFockD

theorem quad_fockD : ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ι → ℕ)
    (φ : (∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    ∀ (Ψ : (⨂[ℂ] w : ι, Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)) →ₗ[ℂ] Sch l),
    (∀ c T, Ψ (sumPl (fun w => heisOp (c w)) T) = dRho (φ c) (Ψ T)) →
    ∀ Y : ∀ w : ι, Mat (R w) (S w), (∀ w, Y w ∈ upq (R w) (S w)) → ∀ Z : Matrix (l ⊕ l) (l ⊕ l) ℝ,
    (∀ c, Z *ᵥ φ c = φ fun w => c w * (Y w)ᵀ) →
    ∀ T, quad Z (Ψ T) = Ψ (sumPl (fun w => fockAct2 (P w) (Q w) (R w) (S w) (Y w)) T) := by
  intro ι l _ _ _ _ P Q R S φ hφ Ψ hΨ Y hY Z hZ T
  have hq := GlobalTheory.T.metaplecticQuadraticOperator_eq_sum_symplectic_dual l (Idx P Q R S) Z (fun i => φ (QuadFockD.cu i)) (fun i => φ (QuadFockD.cv i))
    (QuadFockD.dual φ hφ)
  have hop : sumPl (V := fun w => Pol (P w) (Q w) (R w) (S w)) (fun w => fockAct2 (P w) (Q w) (R w) (S w) (Y w)) =
      (4 * Real.pi * Complex.I : ℂ)⁻¹ • ∑ i : Idx P Q R S, (1 / 2 : ℂ) •
        (sumPl (V := fun w => Pol (P w) (Q w) (R w) (S w)) (fun w => heisOp (QuadFockD.cu i w * (Y w)ᵀ)) *
            sumPl (V := fun w => Pol (P w) (Q w) (R w) (S w)) (fun w => heisOp (QuadFockD.cv i w)) +
          sumPl (V := fun w => Pol (P w) (Q w) (R w) (S w)) (fun w => heisOp (QuadFockD.cv i w)) *
            sumPl (V := fun w => Pol (P w) (Q w) (R w) (S w)) (fun w => heisOp (QuadFockD.cu i w * (Y w)ᵀ))) := by
    rw [sum_idx]
    simp only [QuadFockD.cu_true_mul, QuadFockD.cu_false_mul, QuadFockD.cv_true, QuadFockD.cv_false, sumPl_singleD,
      heisOp_smul]
    unfold sumPl
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    dsimp only
    rw [GlobalTheory.T.fockAct2_eq_symmetrised_heisenbergQuadratic (P w) (Q w) (R w) (S w) (Y w) (hY w)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← atPlLin_apply, map_smul, map_sum, map_sub, map_add (f := _), atPlLin_mul]
    congr 1
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [lineSign_eq_sgn]
    simp only [smul_mul_assoc, mul_smul_comm]
    push_cast
    module
  rw [hop, hq]
  clear hq hop hφ hY
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.add_apply, Module.End.mul_apply, map_smul, map_sum, map_add, hΨ, hZ]

end GlobalTheory.HoweD
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionQuadraticOperatorsFactorSignaturesStatement
open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil
open GlobalTheory.HoweD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockAction_quadraticOperators_factorSignatures : ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ι → ℕ)
    (φ : (∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    ∀ (Ψ : (⨂[ℂ] w : ι, Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)) →ₗ[ℂ] Sch l),
    (∀ c T, Ψ (sumPl (fun w => heisOp (c w)) T) = dRho (φ c) (Ψ T)) →
    ∀ Y : ∀ w : ι, Mat (R w) (S w), (∀ w, Y w ∈ upq (R w) (S w)) → ∀ Z : Matrix (l ⊕ l) (l ⊕ l) ℝ,
    (∀ c, Z *ᵥ φ c = φ fun w => c w * (Y w)ᵀ) →
    ∀ T, quad Z (Ψ T) = Ψ (sumPl (fun w => fockAct2 (P w) (Q w) (R w) (S w) (Y w)) T) := by
  first | exact @GlobalTheory.HoweD.quad_fockD | exact GlobalTheory.HoweD.quad_fockD | (intros; apply GlobalTheory.HoweD.quad_fockD <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticHomOfUnitaryTransposeAction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticHomOfUnitaryTransposeAction
open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil
open GlobalTheory.HoweD

noncomputable section

namespace GlobalTheory.ColActionD

theorem exists_symplectic_hom_of_unitary_dep : ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ι → ℕ)
    (φ : (∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    ∀ (G : Type) [Group G] [TopologicalSpace G] (k : G →* (∀ w : ι, Mat (R w) (S w))), Continuous k →
    (∀ g w, (k g w)ᴴ * Jm (R w) (S w) * k g w = Jm (R w) (S w)) →
    ∃ s : G →* Matrix.symplecticGroup l ℝ, Continuous s ∧
      ∀ g c, (s g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ φ c = φ fun w => c w * (k g w)ᵀ := by
  intro ι l _ _ _ _ P Q R S φ hφ G _ _ k hk hkJ
  let A : G → (∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) →ₗ[ℝ]
      (∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) := fun g =>
    { toFun := fun c w => c w * (k g w)ᵀ
      map_add' := fun c c' => by ext w : 1; simp [Matrix.add_mul]
      map_smul' := fun r c => by ext w : 1; simp [Matrix.smul_mul] }
  let T : G → (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ) := fun g => φ.toLinearMap ∘ₗ A g ∘ₗ φ.symm.toLinearMap
  have hT : ∀ g c, T g (φ c) = φ (fun w => c w * (k g w)ᵀ) := fun g c => by simp [T, A]
  have hsy : ∀ g u v, sympl (T g u) (T g v) = sympl u v := by
    intro g u v
    obtain ⟨c, rfl⟩ := φ.surjective u
    obtain ⟨c', rfl⟩ := φ.surjective v
    rw [hT, hT, hφ, hφ]
    simp only [GlobalTheory.ColAction.signed_sum_mul_transpose _ _ _ (hkJ g _)]
  have hmem : ∀ g, LinearMap.toMatrix' (T g) ∈ Matrix.symplecticGroup l ℝ := fun g =>
    GlobalTheory.ColAction.mem_symplecticGroup_of_sympl _
      (fun u v => by simpa only [LinearMap.toMatrix'_mulVec] using hsy g u v)
  have hTmul : ∀ g h, T (g * h) = T g ∘ₗ T h := by
    intro g h
    apply LinearMap.ext
    intro u
    obtain ⟨c, rfl⟩ := φ.surjective u
    show T (g * h) (φ c) = T g (T h (φ c))
    rw [hT, hT, hT]
    congr 1
    ext w : 1
    simp [map_mul, Pi.mul_apply, Matrix.transpose_mul, Matrix.mul_assoc]
  have hT1 : T 1 = LinearMap.id := by
    apply LinearMap.ext
    intro u
    obtain ⟨c, rfl⟩ := φ.surjective u
    rw [hT]
    simp
  let s : G →* Matrix.symplecticGroup l ℝ :=
    { toFun := fun g => ⟨LinearMap.toMatrix' (T g), hmem g⟩
      map_one' := by
        apply Subtype.ext
        simp only [hT1, LinearMap.toMatrix'_id]
        rfl
      map_mul' := fun g h => by
        apply Subtype.ext
        simp only [hTmul, LinearMap.toMatrix'_comp]
        rfl }
  refine ⟨s, ?_, fun g c => ?_⟩
  · apply Continuous.subtype_mk
    refine continuous_pi fun a => continuous_pi fun b => ?_
    have e : ∀ g, LinearMap.toMatrix' (T g) a b = φ (fun w => φ.symm (Pi.single b 1) w * (k g w)ᵀ) a := by
      intro g
      rw [LinearMap.toMatrix'_apply, ← hT, φ.apply_symm_apply]
    simp only [e]
    exact (continuous_apply a).comp ((LinearMap.continuous_of_finiteDimensional φ.toLinearMap).comp
      (continuous_pi fun w => continuous_const.matrix_mul ((continuous_apply w).comp hk).matrix_transpose))
  · show LinearMap.toMatrix' (T g) *ᵥ φ c = _
    rw [LinearMap.toMatrix'_mulVec, hT]

end GlobalTheory.ColActionD
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticHomOfUnitaryTransposeActionStatement
open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil
open GlobalTheory.HoweD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symplectic_hom_of_unitary_transpose_action : ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ι → ℕ)
    (φ : (∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    ∀ (G : Type) [Group G] [TopologicalSpace G] (k : G →* (∀ w : ι, Mat (R w) (S w))), Continuous k →
    (∀ g w, (k g w)ᴴ * Jm (R w) (S w) * k g w = Jm (R w) (S w)) →
    ∃ s : G →* Matrix.symplecticGroup l ℝ, Continuous s ∧
      ∀ g c, (s g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ φ c = φ fun w => c w * (k g w)ᵀ := by
  first | exact @GlobalTheory.ColActionD.exists_symplectic_hom_of_unitary_dep | exact GlobalTheory.ColActionD.exists_symplectic_hom_of_unitary_dep | (intros; apply GlobalTheory.ColActionD.exists_symplectic_hom_of_unitary_dep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionNormalisingSchrodinger
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionNormalisingSchrodinger
open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil Matrix

noncomputable section

namespace GlobalTheory.HoweD.Osc

variable {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ι → ℕ}

abbrev Lines (P Q R S : ι → ℕ) := Σ o : (Σ w : ι, Ix (P w) (Q w)), Ix (R o.1) (S o.1)

def lineSgn (n : Lines P Q R S) : Bool :=
  linePos (p := P n.1.1) (q := Q n.1.1) (r := R n.1.1) (s := S n.1.1) (n.1.2, n.2)

theorem blockDiagonal'_mulVec_apply {m : (Σ w : ι, Ix (P w) (Q w)) → Type} [∀ o, Fintype (m o)]
    [∀ o, DecidableEq (m o)] (M : ∀ o, Matrix (m o) (m o) ℂ) (v : (Σ o, m o) → ℂ) (o : Σ w : ι, Ix (P w) (Q w))
    (b : m o) : (blockDiagonal' M *ᵥ v) ⟨o, b⟩ = ∑ b', M o b b' * v ⟨o, b'⟩ := by
  simp only [mulVec, dotProduct]
  rw [Fintype.sum_sigma, Finset.sum_eq_single o]
  · simp [blockDiagonal'_apply']
  · intro o' _ h
    simp [blockDiagonal'_apply_ne M b _ (Ne.symm h)]
  · simp

theorem diagonal_lineSgn : (diagonal fun n : Lines P Q R S => if lineSgn n then (1 : ℂ) else -1) =
    blockDiagonal' fun o : (Σ w : ι, Ix (P w) (Q w)) => Jm (P o.1) (Q o.1) o.2 o.2 • Jm (R o.1) (S o.1) := by
  ext ⟨o, b⟩ ⟨o', b'⟩
  by_cases h : o = o'
  · subst h
    rcases o with ⟨w, a⟩
    rw [blockDiagonal'_apply']
    rcases a with a | a <;> rcases b with b | b <;> rcases b' with b' | b' <;>
      simp [diagonal_apply, Jm, Formalism.UG.Jpq, lineSgn, linePos, Matrix.one_apply] <;> split_ifs <;> simp_all
  · rw [blockDiagonal'_apply_ne _ _ _ h, diagonal_apply_ne]
    intro e
    exact h (congrArg Sigma.fst e)

theorem blockDiagonal'_mem (M : ∀ w, Mat (R w) (S w)) (hM : ∀ w, (M w)ᴴ * Jm (R w) (S w) * M w = Jm (R w) (S w)) :
    (blockDiagonal' fun o : (Σ w : ι, Ix (P w) (Q w)) => M o.1)ᵀ *
        (diagonal fun n : Lines P Q R S => if lineSgn n then (1 : ℂ) else -1) *
        (blockDiagonal' fun o : (Σ w : ι, Ix (P w) (Q w)) => M o.1).map star =
      diagonal fun n : Lines P Q R S => if lineSgn n then (1 : ℂ) else -1 := by
  rw [diagonal_lineSgn, blockDiagonal'_transpose, blockDiagonal'_map _ _ (star_zero ℂ), ← blockDiagonal'_mul,
    ← blockDiagonal'_mul]
  congr 1
  funext o
  have h := congrArg transpose (hM o.1)
  rw [transpose_mul, transpose_mul, GlobalTheory.SchrodOsc.Jm_transpose] at h
  have e : (M o.1)ᴴᵀ = (M o.1).map star := by ext; simp
  rw [e] at h
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, h]

end GlobalTheory.HoweD.Osc

namespace GlobalTheory.HoweD.Osc

variable {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ι → ℕ} {G : Type} [Group G]

abbrev lineNum (P Q R S : ι → ℕ) := GlobalTheory.SchrodOsc.signEquiv (lineSgn (P := P) (Q := Q) (R := R) (S := S))

abbrev NumIx (P Q R S : ι → ℕ) :=
  Fin (Fintype.card {n // lineSgn (P := P) (Q := Q) (R := R) (S := S) n = true}) ⊕
    Fin (Fintype.card {n // ¬ lineSgn (P := P) (Q := Q) (R := R) (S := S) n = true})

def blockHom (P Q : ι → ℕ) (k : G →* (∀ w, Mat (R w) (S w))) : G →* Matrix (Lines P Q R S) (Lines P Q R S) ℂ where
  toFun g := blockDiagonal' fun o : (Σ w : ι, Ix (P w) (Q w)) => k g o.1
  map_one' := by
    simp only [map_one, Pi.one_apply]
    exact blockDiagonal'_one
  map_mul' g g' := by simp [blockDiagonal'_mul]

def numHom (P Q : ι → ℕ) (k : G →* (∀ w, Mat (R w) (S w))) : G →* Matrix (NumIx P Q R S) (NumIx P Q R S) ℂ :=
  (reindexAlgEquiv ℂ ℂ (lineNum P Q R S)).toAlgHom.toRingHom.toMonoidHom.comp (blockHom P Q k)

theorem numHom_apply (k : G →* (∀ w, Mat (R w) (S w))) (g : G) :
    numHom P Q k g = reindex (lineNum P Q R S) (lineNum P Q R S)
      (blockDiagonal' fun o : (Σ w : ι, Ix (P w) (Q w)) => k g o.1) :=
  rfl

theorem numHom_mem (k : G →* (∀ w, Mat (R w) (S w))) (hk : ∀ g w, (k g w)ᴴ * Jm (R w) (S w) * k g w = Jm (R w) (S w))
    (g : G) :
    (numHom P Q k).toHomUnits g ∈ GlobalTheory.WeilM.UG (Complex.conjAe : ℂ →ₐ[ℝ] ℂ) (fromBlocks 1 0 0 (-1)) := by
  have hc : ⇑(Complex.conjAe : ℂ →ₐ[ℝ] ℂ) = star := funext fun x => by simp
  show (numHom P Q k g)ᵀ * fromBlocks 1 0 0 (-1) * (numHom P Q k g).map (Complex.conjAe : ℂ →ₐ[ℝ] ℂ) =
    fromBlocks 1 0 0 (-1)
  rw [hc, numHom_apply, GlobalTheory.SchrodOsc.fromBlocks_eq_reindex, transpose_reindex]
  have hm : (reindex (lineNum P Q R S) (lineNum P Q R S)
      (blockDiagonal' fun o : (Σ w : ι, Ix (P w) (Q w)) => k g o.1)).map star =
      reindex (lineNum P Q R S) (lineNum P Q R S)
        ((blockDiagonal' fun o : (Σ w : ι, Ix (P w) (Q w)) => k g o.1).map star) := rfl
  rw [hm, ← reindexAlgEquiv_apply ℂ ℂ, ← reindexAlgEquiv_apply ℂ ℂ, ← reindexAlgEquiv_apply ℂ ℂ, ← map_mul, ← map_mul,
    blockDiagonal'_mem _ (hk g)]

def unitHom (P Q : ι → ℕ) (k : G →* (∀ w, Mat (R w) (S w)))
    (hk : ∀ g w, (k g w)ᴴ * Jm (R w) (S w) * k g w = Jm (R w) (S w)) :=
  (numHom P Q k).toHomUnits.codRestrict _ (numHom_mem k hk)

theorem continuous_unitHom [TopologicalSpace G] [IsTopologicalGroup G] (k : G →* (∀ w, Mat (R w) (S w)))
    (hc : Continuous k) (hk : ∀ g w, (k g w)ᴴ * Jm (R w) (S w) * k g w = Jm (R w) (S w)) :
    Continuous (unitHom P Q k hk) := by
  have hn : Continuous (numHom P Q k) := by
    show Continuous fun g => reindex (lineNum P Q R S) (lineNum P Q R S)
      (blockDiagonal' fun o : (Σ w : ι, Ix (P w) (Q w)) => k g o.1)
    exact (Continuous.matrix_blockDiagonal'
      (continuous_pi fun (o : Σ w : ι, Ix (P w) (Q w)) => (continuous_apply o.1).comp hc)).matrix_reindex _ _
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨hn, ?_⟩)
  have : (fun g => (((Subtype.val ∘ unitHom P Q k hk) g)⁻¹ : GL _ ℂ).val) = fun g => numHom P Q k g⁻¹ := by
    funext g
    simp only [Function.comp_apply]
    rw [← Subgroup.coe_inv, ← map_inv]
    rfl
  rw [this]
  exact hn.comp continuous_inv

def coordOf (z : NumIx P Q R S → ℂ) : ∀ w, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ :=
  fun w a b => ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * z (lineNum P Q R S ⟨⟨w, a⟩, b⟩)

theorem coordOf_add (z z' : NumIx P Q R S → ℂ) : coordOf (z + z') = coordOf z + coordOf z' := by
  funext w a b
  simp [coordOf, mul_add]

theorem continuous_coordOf : Continuous (coordOf (P := P) (Q := Q) (R := R) (S := S)) :=
  continuous_pi fun _ => continuous_pi fun _ => continuous_pi fun _ => continuous_const.mul (continuous_apply _)

theorem two_mul_sum_coordOf (z z' : NumIx P Q R S → ℂ) :
    2 * ∑ w, ∑ a, ∑ b, lineSign a b * coordOf z w a b * star (coordOf z' w a b) =
      (∑ i, z (Sum.inl i) * star (z' (Sum.inl i))) - ∑ j, z (Sum.inr j) * star (z' (Sum.inr j)) := by
  set e := lineNum P Q R S with he
  have hs : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * star (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) = 2⁻¹ := by
    rw [star_inv₀, Complex.star_def, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num)]
    push_cast
    rfl
  let F : Lines P Q R S → ℂ := fun n => (if lineSgn n then 1 else -1) * z (e n) * star (z' (e n))
  have h1 : ∀ w a b, lineSign a b * coordOf z w a b * star (coordOf z' w a b) = 2⁻¹ * F ⟨⟨w, a⟩, b⟩ := by
    intro w a b
    simp only [coordOf, F, star_mul, lineSgn, GlobalTheory.SchrodOsc.lineSign_eq]
    rw [← hs, he]
    by_cases h : linePos (a, b) = true <;> simp only [h, ↓reduceIte, Bool.false_eq_true] <;> ring
  have h2 : ∑ n, F n = ∑ w, ∑ a, ∑ b, F ⟨⟨w, a⟩, b⟩ := by
    rw [Fintype.sum_sigma, Fintype.sum_sigma]
  have h3 : ∑ n, F n = ∑ i, F (e.symm i) := (e.symm.sum_comp F).symm
  simp_rw [h1, ← Finset.mul_sum, ← h2, h3, Fintype.sum_sum_type]
  simp only [F, he, GlobalTheory.SchrodOsc.pos_signEquiv_symm_inl, GlobalTheory.SchrodOsc.pos_signEquiv_symm_inr,
    Equiv.apply_symm_apply]
  simp
  ring

theorem coordOf_mulVec (k : G →* (∀ w, Mat (R w) (S w)))
    (hk : ∀ g w, (k g w)ᴴ * Jm (R w) (S w) * k g w = Jm (R w) (S w)) (g : G) (z : NumIx P Q R S → ℂ) :
    coordOf (((unitHom P Q k hk g).1 : Matrix _ _ ℂ) *ᵥ z) = fun w => coordOf z w * (k g w)ᵀ := by
  show coordOf (numHom P Q k g *ᵥ z) = _
  rw [numHom_apply, reindex_apply, submatrix_mulVec_equiv]
  funext w
  ext a b
  simp only [coordOf, Function.comp_apply, Equiv.symm_symm, Equiv.symm_apply_apply]
  rw [blockDiagonal'_mulVec_apply]
  simp only [mul_apply, transpose_apply, Finset.mul_sum, Function.comp_apply]
  exact Finset.sum_congr rfl fun _ _ => by simp only [coordOf, transpose_apply]; ring

end GlobalTheory.HoweD.Osc

open GlobalTheory.HoweD

theorem GlobalTheory.HoweD.exists_osc : ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ι → ℕ)
    (φ : (∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    (∀ v : L2 l, Continuous fun w : l ⊕ l → ℝ => rho w v) →
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (k : G →* (∀ w : ι, Mat (R w) (S w))), Continuous k →
    (∀ g w, (k g w)ᴴ * Jm (R w) (S w) * k g w = Jm (R w) (S w)) →
    ∃ ω : G →* (L2 l ≃ₗᵢ[ℂ] L2 l), (∀ v, Continuous fun g => ω g v) ∧
      ∀ g c v, ω g (rho (φ c) v) = rho (φ fun w => c w * (k g w)ᵀ) (ω g v) := by
  intro ι l _ _ _ _ P Q R S φ hφ hcont G _ _ _ k hkc hk
  obtain ⟨ω₀, hω₀c, hω₀, -⟩ := GlobalTheory.FockRep.exists_unitary_osc _ _ (L2 l)
    (fun z => rho (φ (GlobalTheory.HoweD.Osc.coordOf z)))
    (fun v => (hcont v).comp ((LinearMap.continuous_of_finiteDimensional φ.toLinearMap).comp
      GlobalTheory.HoweD.Osc.continuous_coordOf))
    (fun z z' v => by
      rw [rho_rho, ← map_add (f := _), ← GlobalTheory.HoweD.Osc.coordOf_add, hφ, ← GlobalTheory.HoweD.Osc.two_mul_sum_coordOf]
      congr 2
      simp [Complex.mul_im]
      ring)
  refine ⟨ω₀.comp (GlobalTheory.HoweD.Osc.unitHom P Q k hk), fun v => (hω₀c v).comp (GlobalTheory.HoweD.Osc.continuous_unitHom k hkc hk),
    fun g c v => ?_⟩
  obtain ⟨z, hz⟩ : ∃ z, GlobalTheory.HoweD.Osc.coordOf (P := P) (Q := Q) (R := R) (S := S) z = c := by
    refine ⟨fun i => ((Real.sqrt 2 : ℝ) : ℂ) * (fun n : GlobalTheory.HoweD.Osc.Lines P Q R S => c n.1.1 n.1.2 n.2)
      ((GlobalTheory.HoweD.Osc.lineNum P Q R S).symm i), ?_⟩
    funext w a b
    have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 two_pos).ne'
    simp only [GlobalTheory.HoweD.Osc.coordOf]
    rw [Equiv.symm_apply_apply, ← mul_assoc, inv_mul_cancel₀ h2, one_mul]
  have h := hω₀ (GlobalTheory.HoweD.Osc.unitHom P Q k hk g) z v
  rw [hz, GlobalTheory.HoweD.Osc.coordOf_mulVec, hz] at h
  exact h
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionNormalisingSchrodingerStatement
open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil
open GlobalTheory.HoweD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_oscillator_action_normalising_schrodinger : ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ι → ℕ)
    (φ : (∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    (∀ v : L2 l, Continuous fun w : l ⊕ l → ℝ => rho w v) →
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (k : G →* (∀ w : ι, Mat (R w) (S w))), Continuous k →
    (∀ g w, (k g w)ᴴ * Jm (R w) (S w) * k g w = Jm (R w) (S w)) →
    ∃ ω : G →* (L2 l ≃ₗᵢ[ℂ] L2 l), (∀ v, Continuous fun g => ω g v) ∧
      ∀ g c v, ω g (rho (φ c) v) = rho (φ fun w => c w * (k g w)ᵀ) (ω g v) := by
  first | exact @GlobalTheory.HoweD.exists_osc | exact GlobalTheory.HoweD.exists_osc | (intros; apply GlobalTheory.HoweD.exists_osc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLieRightActionRealCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLieRightActionRealCoordinates
open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil
open GlobalTheory.HoweD

namespace GlobalTheory.HoweD.SpLieD

open Matrix GlobalTheory.RealLift.SpLie

theorem exists_sp_rightActD : ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ι → ℕ)
    (φ : (∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    ∀ Y : ∀ w : ι, Mat (R w) (S w), (∀ w, Y w ∈ upq (R w) (S w)) →
    ∃ Z ∈ LieAlgebra.Symplectic.sp l ℝ, (∀ c, Z *ᵥ φ c = φ fun w => c w * (Y w)ᵀ) ∧
      ∀ (t : ℝ) c, NormedSpace.exp (t • Z) *ᵥ φ c = φ fun w => c w * (NormedSpace.exp (t • Y w))ᵀ := by
  intro ι l _ _ _ _ P Q R S φ hφ Y hY
  let G : (∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) →ₗ[ℝ]
      (∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) :=
    { toFun := fun c w => c w * (Y w)ᵀ
      map_add' := fun c c' => by ext w : 1; simp [Matrix.add_mul]
      map_smul' := fun r c => by ext w : 1; simp [Matrix.smul_mul] }
  set Z := LinearMap.toMatrix' (φ.toLinearMap ∘ₗ G ∘ₗ φ.symm.toLinearMap) with hZdef
  have hZ : ∀ c, Z *ᵥ φ c = φ fun w => c w * (Y w)ᵀ := by
    intro c; rw [hZdef, LinearMap.toMatrix'_mulVec]; simp [G]
  refine ⟨Z, ?_, hZ, ?_⟩
  · refine mem_sp_of_sympl Z fun u v => ?_
    obtain ⟨c, rfl⟩ := φ.surjective u
    obtain ⟨c', rfl⟩ := φ.surjective v
    have hs : (∑ w, ∑ a, ∑ b, lineSign a b * (c w * (Y w)ᵀ) a b * star (c' w a b)) +
        (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star ((c' w * (Y w)ᵀ) a b)) = 0 := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_eq_zero fun w _ => sum_zero _ _ _ (hY w)
    rw [hZ, hZ, hφ, hφ, ← mul_add, ← Complex.add_im]
    simp only [hs, Complex.zero_im, mul_zero]
  · intro t c
    have hpow : ∀ (n : ℕ) (c : ∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ),
        (t • Z) ^ n *ᵥ φ c = φ fun w => c w * ((t • Y w) ^ n)ᵀ := by
      intro n
      induction n with
      | zero => intro c; simp
      | succ n ih =>
        intro c
        rw [pow_succ, ← mulVec_mulVec, Matrix.smul_mulVec, hZ, ← φ.map_smul]
        have : (t • fun w => c w * (Y w)ᵀ) = fun w => c w * (t • Y w)ᵀ := by
          funext w; simp [Matrix.transpose_smul, Matrix.mul_smul]
        rw [this, ih]
        congr 1; funext w
        rw [pow_succ, Matrix.transpose_mul, Matrix.mul_assoc]
    letI : NormedRing (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℝ (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedAlgebra
    have h1 : HasSum (fun n : ℕ => (((n.factorial : ℝ)⁻¹) • (t • Z) ^ n) *ᵥ φ c)
        (NormedSpace.exp (t • Z) *ᵥ φ c) :=
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • Z)).map
        (Matrix.mulVec.addMonoidHomLeft (φ c)) (Continuous.matrix_mulVec continuous_id continuous_const)
    have hw : ∀ w, HasSum (fun n : ℕ => c w * (((n.factorial : ℝ)⁻¹ • (t • Y w) ^ n))ᵀ)
        (c w * (NormedSpace.exp (t • Y w))ᵀ) := by
      intro w
      letI : NormedRing (Mat (R w) (S w)) := Matrix.linftyOpNormedRing
      letI : NormedAlgebra ℝ (Mat (R w) (S w)) := Matrix.linftyOpNormedAlgebra
      have := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • Y w)).matrix_transpose
      exact this.map (AddMonoidHom.mk' (fun M => c w * M) fun _ _ => Matrix.mul_add _ _ _)
        (continuous_const.matrix_mul continuous_id)
    have h2 := (Pi.hasSum.2 hw).map φ (LinearMap.continuous_of_finiteDimensional φ.toLinearMap)
    refine h1.unique ?_
    convert h2 using 1
    funext n
    simp only [Function.comp_apply]
    rw [Matrix.smul_mulVec, hpow, ← φ.map_smul]
    congr 1; funext w
    simp [Matrix.transpose_smul, Matrix.mul_smul]

end GlobalTheory.HoweD.SpLieD
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLieRightActionRealCoordinatesStatement
open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil
open GlobalTheory.HoweD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symplecticLie_right_action_realCoordinates : ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ι → ℕ)
    (φ : (∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    ∀ Y : ∀ w : ι, Mat (R w) (S w), (∀ w, Y w ∈ upq (R w) (S w)) →
    ∃ Z ∈ LieAlgebra.Symplectic.sp l ℝ, (∀ c, Z *ᵥ φ c = φ fun w => c w * (Y w)ᵀ) ∧
      ∀ (t : ℝ) c, NormedSpace.exp (t • Z) *ᵥ φ c = φ fun w => c w * (NormedSpace.exp (t • Y w))ᵀ := by
  first | exact @GlobalTheory.HoweD.SpLieD.exists_sp_rightActD | exact GlobalTheory.HoweD.SpLieD.exists_sp_rightActD | (intros; apply GlobalTheory.HoweD.SpLieD.exists_sp_rightActD <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealMetaplecticRepresentationHolds
theorem GlobalTheory.Published.realMetaplecticRepresentation_holds : GlobalTheory.Published.RealMetaplecticRepresentation :=
  CompanionTheory.ThKR.realMetaplecticRepresentation_holds
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSchwartzGenuineUnitaryRepSignatures
noncomputable section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical
open GlobalTheory.HoweD GlobalTheory.RealWeil GlobalTheory.ArchUniq GlobalTheory.ArchRep

namespace GlobalTheory.ArchRepD

theorem archRepD :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F κ), IsCMExt F E σ → IsStd ψ →
    FramedD τ JA JB a b A C → IsFockMapD ψ τ d A C Φ →
    ∃ (ρ : UG (cA σ) JB →* (SInf F κ →L[ℂ] SInf F κ)) (c₀ : InfinitePlace F → ℂ),
      (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
        (∀ u : Matrix α β (AE F E), At (evI F) u → ∀ f f₁ : SInf F κ,
          (∀ h : (κ → Af F) → ℂ, d.rho ψ u (pureA F f h) = pureA F f₁ h) →
            ∀ h : (κ → Af F) → ℂ, d.rho ψ (actB (cA σ) g u) (pureA F (ρ g f) h) = pureA F (ρ g f₁) h) ∧
        ∀ ν : Measure (κ → mixedEmbedding.mixedSpace F), ν.IsAddHaarMeasure → ∀ f₁ f₂ : SInf F κ,
          ∫ x, star (ρ g f₁ x) * ρ g f₂ x ∂ν = ∫ x, star (f₁ x) * f₂ x ∂ν) ∧
      (∀ (L : SInf F κ →L[ℂ] ℂ) (f : SInf F κ),
        ContinuousOn (fun g => L (ρ g f)) {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)}) ∧
      ∀ γ ∈ RLines (σ := σ) JB, ∀ Y, IsGenD τ C γ Y → ∀ (T : TensD F P Q R S) (L : SInf F κ →L[ℂ] ℂ),
        HasDerivAt (fun t : ℝ => L (ρ (γ (Multiplicative.ofAdd t)) (Φ T)))
          (L (Φ (sumPl (fun w => fockAct2 (P w) (Q w) (R w) (S w) (Y w) + (c₀ w * (Y w).trace) • 1) T))) 0 := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C Φ hCM hψ hFr hΦ
  obtain ⟨n, θ, φ, φ₀, hp, hq, hφ, hφu⟩ := GlobalTheory.T.exists_archimedean_phaseSpace_coordinates_placeSignatures F E σ α β κ P Q R S τ JA JB d a b A C hCM hFr
  obtain ⟨k, hkc, hkC, hkJ, hcan⟩ := GlobalTheory.T.exists_continuous_hom_unitary_realPlaces_placewise_signature F E σ β R S τ JB b C hCM hFr.2.2
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨ω, hωc, hωi⟩ := GlobalTheory.T.exists_oscillator_action_normalising_schrodinger _ _ P Q R S φ hφ (GlobalTheory.T.continuous_rho_apply _) (UG (cA σ) JB) k hkc hkJ
  obtain ⟨s, hsc, hsφ⟩ := GlobalTheory.T.exists_symplectic_hom_of_unitary_transpose_action _ _ P Q R S φ hφ (UG (cA σ) JB) k hkc hkJ
  obtain ⟨ρ, η, hη1, hη2, hη3, hρi, hρu, hρc, hρd⟩ :=
    realRep GlobalTheory.Published.realMetaplecticRepresentation_holds s hsc ω hωc fun g w v => by
      obtain ⟨c, rfl⟩ := φ.surjective w
      rw [hsφ, hωi]
  obtain ⟨kk, hkk⟩ := GlobalTheory.T.deriv_continuous_character_real_unitary_one_parameter F E σ β R S τ JB b C hCM hFr.2.2 η (fun g h _ _ => hη1 g h) hη2.continuousOn
    fun g _ => hη3 g
  let toE : SInf F κ →L[ℂ] Sch (Fin n) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) θ.symm
  let toV : Sch (Fin n) →L[ℂ] SInf F κ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) θ
  have htoE : ∀ g, ⇑(toE g) = ⇑g ∘ ⇑θ.symm := fun g => rfl
  have htoV : ∀ h, ⇑(toV h) = ⇑h ∘ ⇑θ := fun h => rfl
  have hVE : ∀ g, toV (toE g) = g := fun g => by ext x; simp [htoE, htoV]
  have hEV : ∀ h, toE (toV h) = h := fun h => by ext x; simp [htoE, htoV]
  clear_value toE toV
  have hS := SchrTransport.schr_coords (trP F κ) θ φ₀ hp hq
  let ρ' : UG (cA σ) JB →* (SInf F κ →L[ℂ] SInf F κ) :=
    { toFun := fun g => toV ∘L ρ g ∘L toE
      map_one' := ContinuousLinearMap.ext fun f => by
        rw [map_one]
        exact hVE f
      map_mul' := fun g h => ContinuousLinearMap.ext fun f => by
        simp only [map_mul, ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply, hEV] }
  have hρ' : ∀ g f, ρ' g f = toV (ρ g (toE f)) := fun _ _ => rfl
  clear_value ρ'
  refine ⟨ρ', fun w => kk w / 2, fun g _ => ⟨fun u hu f f₁ hf h => ?_, fun ν hν f₁ f₂ => ?_⟩, fun L f => ?_,
    fun γ hγ Y hY T L => ?_⟩
  · choose A' hA' using fun w => (hFr.2.1 w).2
    choose C' hC' using fun w => (hFr.2.2 w).2
    obtain ⟨c, hc⟩ : ∃ c : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ,
        ∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ :=
      ⟨fun w => A' w * u.map (piInf (τ w)) * (C' w)ᵀ, fun w => by
        have : (C' w)ᵀ * (C w)ᵀ = 1 := by rw [← Matrix.transpose_mul, hC', Matrix.transpose_one]
        simp only [Matrix.mul_assoc]
        rw [this, Matrix.mul_one, ← Matrix.mul_assoc, hA', Matrix.one_mul]⟩
    have hu' : At (evI F) (actB (cA σ) g u) := fun t ht => by
      rw [actB, ← Matrix.smul_mul, hu t ht, Matrix.zero_mul]
    have hc' : ∀ w, (actB (cA σ) g u).map (piInf (τ w)) = A w * (c w * (k g w)ᵀ) * (C w)ᵀ := fun w => by
      rw [actB, Matrix.map_mul, hc, Matrix.transpose_map, Matrix.mul_assoc, ← Matrix.transpose_mul, hkC,
        Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
    have e1 : ⇑f₁ = schrF (trP F κ) (locV (d.e u).1, locV (d.e u).2) ⇑f := by
      funext y
      have := congrFun ((GlobalTheory.T.heisenbergOp_archimedean_vector_acts_by_schrodinger_trace F E σ α β κ ψ JA JB d hψ u hu f fun _ => 1).symm.trans (hf fun _ => 1)) (liftV y)
      simp only [pureA, liftV, Prod.fst, RingEquiv.apply_symm_apply, mul_one] at this
      exact this.symm
    have e2 : ⇑(toE f₁) = rhoFun (φ c) ⇑(toE f) := by
      have := hS (locV (d.e u).1, locV (d.e u).2) ⇑(toE f)
      rw [← htoV, hVE, ← e1, ← hφu u c hu hc] at this
      rw [htoE, this]
      funext x
      simp
    have e3 := hρi g _ _ _ e2
    rw [hsφ, hφu _ _ hu' hc'] at e3
    rw [GlobalTheory.T.heisenbergOp_archimedean_vector_acts_by_schrodinger_trace F E σ α β κ ψ JA JB d hψ _ hu', hρ', hρ', htoV, htoV, hS, e3]
  · haveI : BorelSpace ({w : InfinitePlace F // w.IsReal} → ℝ) := Pi.borelSpace
    haveI : BorelSpace ({w : InfinitePlace F // w.IsComplex} → ℂ) := Pi.borelSpace
    haveI : BorelSpace (mixedEmbedding.mixedSpace F) := Prod.borelSpace
    haveI : BorelSpace (κ → mixedEmbedding.mixedSpace F) := Pi.borelSpace
    obtain ⟨r, hr⟩ := haar_coords ν θ
    rw [hr, hr]
    congr 1
    simp only [hρ', htoV, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
    rw [hρu]
    simp only [htoE, Function.comp_apply]
  · simp only [hρ']
    exact (hρc (L ∘L toV) (toE f)).continuousOn
  · have hkY : ∀ (t : ℝ) w, k (γ (Multiplicative.ofAdd t)) w = NormedSpace.exp (t • Y w) := fun t w =>
      hcan w _ _ ((hkC _ w).symm.trans (hY t w))
    have hYu : ∀ w, Y w ∈ upq (R w) (S w) := fun w => GlobalTheory.RealLiftGen.mem_upq_of (Y w) fun t => by
      have := congrArg (fun X => X.map star) (hkJ (γ (Multiplicative.ofAdd t)) w)
      simp only [GlobalTheory.RealLiftGen.map_star_mul, GlobalTheory.RealLiftGen.Jm_map_star, hkY] at this
      refine Eq.trans ?_ this
      congr 2
      ext i j
      simp
    obtain ⟨Z, hZ, hZφ, hZe⟩ := GlobalTheory.T.exists_symplecticLie_right_action_realCoordinates _ _ P Q R S φ hφ Y hYu
    have hsZ : ∀ t : ℝ, (s (γ (Multiplicative.ofAdd t)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) =
        NormedSpace.exp (t • Z) := fun t => Matrix.toLin'.injective (LinearMap.ext fun v => by
      obtain ⟨c, rfl⟩ := φ.surjective v
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
      calc
        _ = φ (fun w => c w * (k (γ (Multiplicative.ofAdd t)) w)ᵀ) := hsφ _ _
        _ = _ := by simp only [hkY, ← hZe])
    have hd := hρd (fun t => γ (Multiplicative.ofAdd t)) (hγ.1.comp continuous_ofAdd) (by change γ 1 = 1; exact map_one γ) Z hZ hsZ _
      (hkk γ hγ Y hY) (L ∘L toV) (toE (Φ T))
    obtain ⟨D, hD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ α β κ ψ JA JB d hψ
    have hΨ : ∀ c T, (toE.toLinearMap ∘ₗ Φ) (sumPl (fun w => heisOp (c w)) T) = dRho (φ c) ((toE.toLinearMap ∘ₗ Φ) T) := by
      intro c T
      obtain ⟨u, ⟨hu, hc⟩, -⟩ := GlobalTheory.T.existsUnique_archimedeanMatrix_adeleExtension_of_components σ τ hCM fun w => A w * c w * (C w)ᵀ
      have e1 := (GlobalTheory.RealLift.actsLaws F κ (Φ T) _ _).2.2.2.2 _ (hΦ.2 u hu c hc T) (hD u hu (Φ T)).1
      ext x
      obtain ⟨y, rfl⟩ := θ.surjective x
      have e2 := SchrTransport.dRho_coords (trP F κ) θ φ₀ hp hq (locV (d.e u).1, locV (d.e u).2) (Φ T) (toE (Φ T))
        (by rw [← htoV, hVE]) y
      rw [← hφu u c hu hc] at e2
      simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
      rw [← e2, e1, htoE, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
      exact (hD u hu (Φ T)).2 y
    have e3 := GlobalTheory.T.fockAction_quadraticOperators_factorSignatures _ _ P Q R S φ hφ _ hΨ Y hYu Z hZφ T
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe] at e3
    have hf : (fun t : ℝ => L (ρ' (γ (Multiplicative.ofAdd t)) (Φ T))) =
        (fun t : ℝ => L (toV (ρ (γ (Multiplicative.ofAdd t)) (toE (Φ T))))) := by
      funext t
      exact congrArg L (hρ' (γ (Multiplicative.ofAdd t)) (Φ T))
    rw [hf]
    refine hd.congr_deriv ?_
    rw [e3, sumPl_add_smul]
    simp only [ContinuousLinearMap.comp_apply, hVE, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
      map_add, map_smul, smul_eq_mul, Finset.sum_div]
    congr 2
    exact Finset.sum_congr rfl fun w _ => by ring

end GlobalTheory.ArchRepD

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSchwartzGenuineUnitaryRepSignaturesStatement
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical
open GlobalTheory.HoweD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanSchwartz_genuineUnitaryRep_signatures : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F κ), IsCMExt F E σ → IsStd ψ →
    FramedD τ JA JB a b A C → IsFockMapD ψ τ d A C Φ →
    ∃ (ρ : UG (cA σ) JB →* (SInf F κ →L[ℂ] SInf F κ)) (c₀ : InfinitePlace F → ℂ),
      (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
        (∀ u : Matrix α β (AE F E), At (evI F) u → ∀ f f₁ : SInf F κ,
          (∀ h : (κ → Af F) → ℂ, d.rho ψ u (pureA F f h) = pureA F f₁ h) →
            ∀ h : (κ → Af F) → ℂ, d.rho ψ (actB (cA σ) g u) (pureA F (ρ g f) h) = pureA F (ρ g f₁) h) ∧
        ∀ ν : Measure (κ → mixedEmbedding.mixedSpace F), ν.IsAddHaarMeasure → ∀ f₁ f₂ : SInf F κ,
          ∫ x, star (ρ g f₁ x) * ρ g f₂ x ∂ν = ∫ x, star (f₁ x) * f₂ x ∂ν) ∧
      (∀ (L : SInf F κ →L[ℂ] ℂ) (f : SInf F κ),
        ContinuousOn (fun g => L (ρ g f)) {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)}) ∧
      ∀ γ ∈ RLines (σ := σ) JB, ∀ Y, IsGenD τ C γ Y → ∀ (T : TensD F P Q R S) (L : SInf F κ →L[ℂ] ℂ),
        HasDerivAt (fun t : ℝ => L (ρ (γ (Multiplicative.ofAdd t)) (Φ T)))
          (L (Φ (sumPl (fun w => fockAct2 (P w) (Q w) (R w) (S w) (Y w) + (c₀ w * (Y w).trace) • 1) T))) 0 := by
  first | exact @GlobalTheory.ArchRepD.archRepD | exact GlobalTheory.ArchRepD.archRepD | (intros; apply GlobalTheory.ArchRepD.archRepD <;> assumption)
end
