module

public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutDef
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurLemmaHeisenbergCommutingThetaOperator
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.ContinuousTheta

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.IntegralMul
open scoped TensorProduct Matrix Kronecker
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace PositivityTheory.ThKW.PhaseFourierInjectivity

open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {nS nT : ℕ}

theorem hOF_eq_trace {m : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (J : Matrix (Fin m) (Fin m) E) (x y : WOF F E nS m) :
    hOF σ JS J x y = (JS⁻¹.map (incAF F E) * ((y.map (cAF σ))ᵀ * J.map (incAF F E) * x)).trace := by
  simp only [hOF, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Finset.mul_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  ring

theorem dC_dual (J : Matrix (Fin nT) (Fin nT) E) (hJ : J.det ≠ 0) :
    (dC E nT)ᵀ * GlobalTheory.WeilSchrodinger.DblTargetF.dblG J * dCdE J = 1 := by
  have e : GlobalTheory.WeilSchrodinger.DblTargetF.dblG J = (dbl J).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := rfl
  rw [e, dCdE, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id,
    diagCols, dbl, Matrix.transpose_fromRows, Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows]
  simp only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_zero, add_zero, zero_add, neg_mul_neg, Matrix.neg_mul,
    Matrix.mul_neg, neg_neg, Matrix.mul_smul, Matrix.mul_nonsing_inv _ (Ne.isUnit hJ), ← add_smul]
  norm_num

theorem dC_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (n : ℕ) : (dC R n).map φ = dC S n := by
  ext i j
  obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective i
  simp only [dC, diagCols, Matrix.map_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id]
  rcases k with k | k <;> simp [Matrix.one_apply, apply_ite φ]

theorem hOF_dual (JS : Matrix (Fin nS) (Fin nS) E) (J : Matrix (Fin nT) (Fin nT) E) (hJ : J.det ≠ 0) (v y : WOF F E nS nT) :
    hOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J) (dCd F J * v) (dC (AF F ⊗[F] E) nT * y) =
      (JS⁻¹.map (incAF F E) * ((y.map (cAF σ))ᵀ * v)).trace := by
  have h := congrArg (fun M : Matrix (Fin nT) (Fin nT) E => M.map (incAF F E)) (dC_dual J hJ)
  simp only [Matrix.map_mul, Matrix.transpose_map, dC_map] at h
  rw [Matrix.map_one _ (map_zero _) (map_one _)] at h
  rw [hOF_eq_trace, Matrix.map_mul, dC_map, Matrix.transpose_mul]
  congr 2
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ (dCd F J), ← Matrix.mul_assoc (dC _ nT)ᵀ, ← Matrix.mul_assoc (dC _ nT)ᵀ]
  rw [show (dC (AF F ⊗[F] E) nT)ᵀ * (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J).map (incAF F E) * dCd F J = 1 from h,
    Matrix.one_mul]

theorem phase_move (JS : Matrix (Fin nS) (Fin nS) E) (J : Matrix (Fin nT) (Fin nT) E) (hJ : J.det ≠ 0) (ξ₀ : E)
    (ψ : AddChar (AF F) ℂ) (s : GL (Fin nT) (AF F ⊗[F] E)) (y w : WOF F E nS nT) :
    phase σ JS J ξ₀ ψ ((s⁻¹).1 * y) ((s.1.map (cAF σ))ᵀ * w) = phase σ JS J ξ₀ ψ y w := by
  unfold phase symplOF
  rw [hOF_dual JS J hJ, hOF_dual JS J hJ, Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc _ (s.1.map (cAF σ))ᵀ, ← Matrix.transpose_mul, ← Matrix.map_mul, Units.mul_inv,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.one_mul]


variable (F E nS nT) in
def vecE : WOF F E nS nT ≃+ (Fin (nT * nS) → AF F ⊗[F] E) where
  toFun w k := w (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  invFun u i j := u (finProdFinEquiv (i, j))
  left_inv w := by ext i j; simp only [Equiv.symm_apply_apply]
  right_inv u := by ext k; simp only [Prod.mk.eta, Equiv.apply_symm_apply]
  map_add' _ _ := rfl

theorem integral_mul (ν : Measure (WOF F E nS nT)) (hν : ν.IsAddHaarMeasure) (A : GL (Fin nT) (AF F ⊗[F] E))
    (g : WOF F E nS nT → ℂ) : ∫ w, g (A.1 * w) ∂ν =
      ((((distribHaarChar (AF F) (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F)
        (Matrix.GeneralLinearGroup.det A)) : ℝ) ^ nS)⁻¹ : ℝ) : ℂ) * ∫ w, g w ∂ν := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.T.rationalMatrices_discrete_cocompact_adelicMatrixSpace F E nS nT
  have := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  have : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  letI : MeasurableSpace (Fin (nT * nS) → AF F ⊗[F] E) := borel _
  have : BorelSpace (Fin (nT * nS) → AF F ⊗[F] E) := ⟨rfl⟩
  have c1 : Continuous (vecE F E nS nT) :=
    continuous_pi fun k => (continuous_apply (finProdFinEquiv.symm k).2).comp (continuous_apply (finProdFinEquiv.symm k).1)
  have c2 : Continuous (vecE F E nS nT).symm := continuous_pi fun i => continuous_pi fun j => continuous_apply _
  let eh : WOF F E nS nT ≃ₜ (Fin (nT * nS) → AF F ⊗[F] E) := .mk (vecE F E nS nT).toEquiv c1 c2
  let em := eh.toMeasurableEquiv
  let K : Matrix (Fin nT) (Fin nT) (AF F ⊗[F] E) → Matrix (Fin (nT * nS)) (Fin (nT * nS)) (AF F ⊗[F] E) :=
    fun M => (M ⊗ₖ (1 : Matrix (Fin nS) (Fin nS) (AF F ⊗[F] E))).submatrix finProdFinEquiv.symm finProdFinEquiv.symm
  have hK : ∀ M M', M * M' = 1 → K M * K M' = 1 := fun M M' h => by
    simp only [K]
    rw [Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul, h, Matrix.mul_one, Matrix.one_kronecker_one,
      Matrix.submatrix_one_equiv]
  let t : GL (Fin (nT * nS)) (AF F ⊗[F] E) := ⟨K A.1, K (A⁻¹).1, hK _ _ A.mul_inv, hK _ _ A.inv_mul⟩
  have hd : Matrix.GeneralLinearGroup.det t = Matrix.GeneralLinearGroup.det A ^ nS := by
    ext
    rw [Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
    show (K A.1).det = _
    simp only [K]
    rw [Matrix.det_submatrix_equiv_self, Matrix.det_kronecker, Matrix.det_one, one_pow, mul_one, Fintype.card_fin]
  have hv : ∀ w : WOF F E nS nT, (vecE F E nS nT).symm (t.1 *ᵥ vecE F E nS nT w) = A.1 * w := fun w => by
    ext i j
    show ∑ k, K A.1 (finProdFinEquiv (i, j)) k * vecE F E nS nT w k = ∑ k, A.1 i k * w k j
    rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    show ∑ b, K A.1 (finProdFinEquiv (i, j)) (finProdFinEquiv (a, b)) *
      w (finProdFinEquiv.symm (finProdFinEquiv (a, b))).1 (finProdFinEquiv.symm (finProdFinEquiv (a, b))).2 = _
    simp only [K, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.kroneckerMap_apply, Matrix.one_apply]
    simp
  have h := GlobalTheory.T.integral_adelicGL_mulVec_haar_eq_modulus_det F E _ t (ν.map em) ((vecE F E nS nT).isAddHaarMeasure_map ν c1 c2)
    (fun u => g ((vecE F E nS nT).symm u))
  rw [integral_map_equiv, integral_map_equiv, hd, map_pow, map_pow, NNReal.coe_pow] at h
  refine Eq.trans ?_ (h.trans ?_)
  · congr 1
    funext w
    exact congrArg g (hv w).symm
  · congr 2
    funext w
    exact congrArg g ((vecE F E nS nT).symm_apply_apply w)

end

theorem change : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
    ∀ (s : GL (Fin nT) (AF F ⊗[F] E)) (N : WOF F E nS nT → ℂ), Continuous N → Integrable N ν →
      Continuous (fun w : WOF F E nS nT => N ((s.1.map (cAF σ))ᵀ * w)) ∧
      Integrable (fun w : WOF F E nS nT => N ((s.1.map (cAF σ))ᵀ * w)) ν ∧
      ∀ y : WOF F E nS nT, ∫ v, phase σ JS JT ξ₀ B.ψ ((s⁻¹).1 * y) v * N v ∂ν =
        ((mfac F E nS s : ℝ) : ℂ) ^ 2 * ∫ w, phase σ JS JT ξ₀ B.ψ y w * N ((s.1.map (cAF σ))ᵀ * w) ∂ν := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσ ν 𝓕 hν h𝓕 s N hN hI
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.T.rationalMatrices_discrete_cocompact_adelicMatrixSpace F E nS nT
  have := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  have : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  have hA : ∀ M M' : Matrix (Fin nT) (Fin nT) (AF F ⊗[F] E), M * M' = 1 → (M'.map (cAF σ))ᵀ * (M.map (cAF σ))ᵀ = 1 :=
    fun M M' h => by
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  let A : GL (Fin nT) (AF F ⊗[F] E) := ⟨(s.1.map (cAF σ))ᵀ, ((s⁻¹).1.map (cAF σ))ᵀ, hA _ _ s.inv_mul, hA _ _ s.mul_inv⟩
  let e : WOF F E nS nT ≃+ WOF F E nS nT :=
    { toFun := fun w => A.1 * w
      invFun := fun w => (A⁻¹).1 * w
      left_inv := fun w => by simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      right_inv := fun w => by simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      map_add' := fun v w => Matrix.mul_add _ v w }
  have c1 : Continuous e := continuous_const.matrix_mul continuous_id
  have c2 : Continuous e.symm := continuous_const.matrix_mul continuous_id
  refine ⟨hN.comp c1, ?_, fun y => ?_⟩
  · have : (ν.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map ν c1 c2
    obtain ⟨c, hc⟩ : ∃ c : NNReal, ν.map e = c • ν := ⟨_, Measure.isAddLeftInvariant_eq_smul _ ν⟩
    have h1 : Integrable N (ν.map e) := by
      rw [hc]
      exact hI.smul_measure_nnreal
    exact (integrable_map_measure hN.aestronglyMeasurable c1.measurable.aemeasurable).1 h1
  · have h := integral_mul ν hν A (fun v => phase σ JS JT ξ₀ B.ψ ((s⁻¹).1 * y) v * N v)
    have hn : Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) (Matrix.GeneralLinearGroup.det A) =
        Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) (Matrix.GeneralLinearGroup.det s) := by
      refine Units.ext (GlobalTheory.SplitDetCharF.tensor_inj (F := F) (E := E) ?_)
      have hcc : ∀ z : AF F ⊗[F] E, cAF σ (cAF σ z) = z := fun z => by
        induction z using TensorProduct.induction_on with
        | zero => rw [map_zero, map_zero]
        | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (GlobalTheory.SplitDetCharF.sig_invol hB.cm x)
        | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
      have hd : A.1.det = cAF σ s.1.det := by
        show ((s.1.map (cAF σ))ᵀ).det = _
        rw [Matrix.det_transpose, RingHom.map_det]; rfl
      show algebraMap _ _ (Algebra.norm (AF F) A.1.det) = algebraMap _ _ (Algebra.norm (AF F) s.1.det)
      rw [GlobalTheory.SplitDetCharF.algebraMap_norm hB.cm, GlobalTheory.SplitDetCharF.algebraMap_norm hB.cm, hd, hcc, mul_comm]
    rw [hn] at h
    set m : ℝ := (distribHaarChar (AF F) (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F)
      (Matrix.GeneralLinearGroup.det s)) : ℝ) with hm
    have hm0 : 0 < m := NNReal.coe_pos.2 distribHaarChar_pos
    have hf : mfac F E nS s ^ 2 = m ^ nS := by
      show (m ^ ((Fintype.card (Fin nS) : ℝ) / 2)) ^ 2 = _
      rw [← Real.rpow_natCast, ← Real.rpow_mul hm0.le, Fintype.card_fin, ← Real.rpow_natCast]
      congr 1
      push_cast
      ring
    have h2 : (fun w : WOF F E nS nT => phase σ JS JT ξ₀ B.ψ ((s⁻¹).1 * y) (A.1 * w) * N (A.1 * w)) =
        fun w => phase σ JS JT ξ₀ B.ψ y w * N ((s.1.map (cAF σ))ᵀ * w) := funext fun w => by
      rw [← phase_move JS JT hT.2 ξ₀ B.ψ s y w]
    rw [h2] at h
    rw [h, ← Complex.ofReal_pow, hf, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (pow_pos hm0 _).ne',
      Complex.ofReal_one, one_mul]

end PositivityTheory.ThKW.PhaseFourierInjectivity

end
end

section -- merged from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.DiagonalLagrangianIntegralSiegelParabolicTransfoBis
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace PositivityTheory.ThKW.LagrangianIntegralFactorisation

open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation GlobalTheory.ThetaTransform

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end PositivityTheory.ThKW.LagrangianIntegralFactorisation

end
end

section -- merged from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.DiagonalLagrangianIntegralSiegelParabolicTransfoTer
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace PositivityTheory.ThKW.ParsevalPolarization

open GlobalTheory.ThetaTransform

end PositivityTheory.ThKW.ParsevalPolarization

end
end

section -- merged from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.UnitCoef
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace PositivityTheory.ThKW.PhaseFourierInjectivity

open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation

theorem unit_coef : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle) (ωd : GAF σ JS × GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
            Module.End ℂ (WOF F E nS (nT + nT) → ℂ)),
        IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ (μW : Measure (WOF F E nS (nT + nT))) (𝓕W : Set (WOF F E nS (nT + nT))), μW.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS (nT + nT)) 𝓕W μW →
      ∀ (h : GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)) (w₀ : WOF F E nS (nT + nT)) (f : WOF F E nS (nT + nT) → ℂ),
        IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
        ∫ w in 𝓕W, heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ (actOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) 1 h w₀) (ωd (1, h) f) w *
            starRingEnd ℂ (ωd (1, h) f w) ∂μW =
          ∫ w in 𝓕W, heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ w₀ f w * starRingEnd ℂ (f w) ∂μW := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσ χS ωd hω μ 𝓕 hμ h𝓕 h w₀ f hf
  rw [← hω.om_heis 1 h w₀ f hf]
  exact GlobalTheory.ThetaSchurF.scalar_eq hω.std.1.2.1 μ 𝓕 hμ h𝓕 (ωd (1, h)) (hω.om_pres _) (hω.om_unit μ 𝓕 hμ h𝓕 _) _ _
    (GlobalTheory.HeisThetaF.isThetaFunOF_heisOF F E σ B hB _ _ JS _ ξ₀ w₀ f hf) hf

end PositivityTheory.ThKW.PhaseFourierInjectivity

end
end

section -- merged from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SymplOHF
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace PositivityTheory.ThKW.AdelicSchwartzProperties

open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation GlobalTheory.ThetaTransform

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem heis_C {σ : E →ₐ[F] E} {B : Base F E} (hB : B.IsGood σ) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E)
    (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (N : ℕ)
    (α β : WOF F E nS nT ≃ₗ[AF F] (Fin N → AF F)) (e : WOF F E nS (nT + nT) ≃ₗ[AF F] VA F N)
    (hCe : ∀ u v, e (dC (AF F ⊗[F] E) nT * u + dCd F JT * v) = (α v, β u))
    (he : ∀ w w', symplOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ w w' = symV (e w) (e w'))
    (Φ : (Fin N → AF F) → ℂ) (y : WOF F E nS nT) :
    heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ (dC (AF F ⊗[F] E) nT * y) (thV B.ψ Φ ∘ e) =
      thV B.ψ (fun x => B.ψ (x ⬝ᵥ β y) * Φ x) ∘ e := by
  have hCy : e (dC (AF F ⊗[F] E) nT * y) = (0, β y) := by
    have h := hCe y 0
    rw [Matrix.mul_zero, add_zero, map_zero] at h
    exact h
  have h2 : (⅟(2 : AF F)) = algebraMap F (AF F) (1 / 2) := by
    refine invOf_eq_right_inv ?_
    rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul]
    norm_num
  funext w
  simp only [Function.comp_apply, heisOF, thV, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.schr]
  rw [map_add (f := _), hCy]
  have hph : symplOHF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ w (dC (AF F ⊗[F] E) nT * y) =
      ⅟(2 : AF F) * ((e w).1 ⬝ᵥ β y) := by
    rw [symplOHF, he, hCy, h2]
    simp [symV]
  rw [hph, ← tsum_mul_left]
  refine tsum_congr fun ξ => ?_
  set x₁ := (e w).1
  set y₁ := (e w).2
  set b := β y
  set r : Fin N → AF F := fun i => algebraMap F (AF F) (ξ i)
  have hw : e w = (x₁, y₁) := rfl
  simp only [hw, Prod.mk_add_mk, add_zero]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 2
  have h22 : (⅟(2 : AF F)) + ⅟2 = 1 := invOf_two_add_invOf_two
  simp only [dotProduct_add, add_dotProduct]
  linear_combination (x₁ ⬝ᵥ b) * h22

end PositivityTheory.ThKW.AdelicSchwartzProperties

end
end

section -- merged from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutRealB
noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF

namespace PositivityTheory.ThKW

theorem gaussV_eq {κ : Type} [Fintype κ] [DecidableEq κ] {H s g : Matrix κ κ ℂ} (hH : Hᴴ = H) (hQ : (H * s).PosDef)
    (v : κ → ℂ) : gaussV H s g v =
      Complex.exp (-(Real.pi : ℂ) * (star v ⬝ᵥ GlobalTheory.RatAut.RealInt.expM H s g *ᵥ v)) := by
  rw [GlobalTheory.RatAut.RealInt.dot_expM hH hQ, gaussV, omV_apply, omV_apply, jV_apply, ← Complex.exp_add]
  congr 1
  ring

theorem integral_gaussV_B {κ : Type} [Fintype κ] [DecidableEq κ] {H s g g' : Matrix κ κ ℂ} (hH : Hᴴ = H) (hs : s * s = 1)
    (hQ : (H * s).PosDef) (hg : gᴴ * H * g = H) (hc : s * g = g * s) (hi : g * g' = 1) (hd : (g - 1).det ≠ 0) :
    Integrable (gaussV H s g) volume ∧ GlobalTheory.RealWeil.dP s g' ≠ 0 ∧ ∃ r : ℝ, 0 < r ∧
      (∫ v, gaussV H s g v) * (g - 1).det = r * (-s).det * (g.det * GlobalTheory.RealWeil.dP s g') := by
  obtain ⟨-, h1, h2⟩ := GlobalTheory.MatrixGaussian.integral_gaussian κ _ (GlobalTheory.RatAut.RealInt.expM_herm hQ hd)
  have e : gaussV H s g = fun v => Complex.exp (-(Real.pi : ℂ) * (star v ⬝ᵥ GlobalTheory.RatAut.RealInt.expM H s g *ᵥ v)) :=
    funext (gaussV_eq hH hQ)
  refine ⟨by rw [e]; exact h1, ?_, (H * s).det.re⁻¹, inv_pos.2 (Complex.pos_iff.1 hQ.det_pos).1, ?_⟩
  · have h3 := congrArg det (GlobalTheory.RatAut.RealInt.expM_mul hH hs hg hc hi)
    simp only [det_mul] at h3
    have h4 : (-H).det * (-s).det = (H * s).det := by rw [← det_mul, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
    intro h0
    unfold GlobalTheory.RealWeil.dP at h0
    have h5 : (-H).det * (g - 1).det = 0 := by rw [← h3, h0]; ring
    rcases mul_eq_zero.1 h5 with h6 | h6
    · exact hQ.det_pos.ne' (by rw [← h4, h6, zero_mul])
    · exact hd h6
  · rw [e, h2]
    exact GlobalTheory.RatAut.RealInt.gauss_det hH hs hQ hg hc hi hd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}

theorem det_mMF_B (C : Ctx σ B JS JT ξ₀ θ ι) {g : GAF σ JS} {h : GAF σ JT} {a b}
    (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b) :
    (mMF σ JS JT θ (g⁻¹, h⁻¹)).det = ∏ v, tauB B v (b ⊗ₖ aᵀ).det ∧
      (mMF σ JS JT θ (g⁻¹, h⁻¹) - 1).det = ∏ v, tauB B v (b ⊗ₖ aᵀ - 1).det := by
  have e1 : ∀ w, compAtF θ w (mtF σ JT h⁻¹) = b.map (tauB B w) := fun w => by
    rw [show mtF σ JT h⁻¹ = b.map (incAF F E) from hb]
    ext i j
    exact PositivityTheory.ThKW.RealC.theta_inc (C.inf w) _
  have e2 : ∀ w, compAtF θ w (mtF σ JS g⁻¹⁻¹) = a.map (tauB B w) := fun w => by
    rw [inv_inv, show mtF σ JS g = a.map (incAF F E) from ha]
    ext i j
    exact PositivityTheory.ThKW.RealC.theta_inc (C.inf w) _
  have e3 : ∀ w, (b.map (tauB B w) ⊗ₖ (a.map (tauB B w))ᵀ) = (b ⊗ₖ aᵀ).map (tauB B w) := fun w => by
    ext ⟨i, j⟩ ⟨k, l⟩
    simp only [Matrix.kroneckerMap_apply, Matrix.map_apply, Matrix.transpose_apply, map_mul]
  rw [mMF_apply]
  simp only [e1, e2]
  refine ⟨?_, ?_⟩
  · rw [GlobalTheory.RatAut.RealInt.det_blk]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [e3]
    exact (RingHom.map_det _ _).symm
  · rw [GlobalTheory.RatAut.RealInt.det_blk_sub_one]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [e3, RingHom.map_det, map_sub, map_one]
    rfl

end PositivityTheory.ThKW

end
end

section -- merged from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRepBS
noncomputable section

open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.IndefR.DatumF GlobalTheory.FinLatF GlobalTheory.FinWeil

namespace PositivityTheory.ThKW.LatB

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {nS nT : ℕ} {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)}


variable (F) in
def inrA : Af F →ₗ[F] AF F where
  toFun a := pairA F 0 a
  map_add' _ _ := Prod.ext (add_zero 0).symm rfl
  map_smul' c _ := Prod.ext (smul_zero c).symm rfl


variable (F E) in
def liftF : Af F ⊗[F] E →ₗ[F] AEF F E := TensorProduct.map (inrA F) LinearMap.id

theorem liftF_tmul (a : Af F) (t : E) : liftF F E (a ⊗ₜ[F] t) = pairA F 0 a ⊗ₜ[F] t := rfl


variable (E) in
abbrev hatO : AddSubgroup (Af F ⊗[F] E) := GlobalTheory.AdLat.hat1 F (Set.range (algebraMap (𝓞 E) E))

theorem fin_mul_eq (y : AEF F E) :
    algebraMap (AF F) (AEF F E) (pairA F 0 1) * y = liftF F E (finPartF F E y) := by
  induction y using TensorProduct.induction_on with
  | zero => rw [mul_zero, map_zero, map_zero]
  | tmul a t =>
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      show finPartF F E (a ⊗ₜ[F] t) = sndA F a ⊗ₜ[F] t from rfl, liftF_tmul]
    congr 1
    exact Prod.ext (zero_mul _) (one_mul _)
  | add x y hx hy => rw [mul_add, hx, hy, map_add (f := _), map_add (f := _)]

theorem liftF_smul_mem {z : Af F ⊗[F] E} (hz : z ∈ hatO (F := F) E) {u : WOF F E nS nT}
    (hu : u ∈ latOF F E nS nT Λ) : liftF F E z • u ∈ latOF F E nS nT Λ := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, _, ⟨b, rfl⟩, rfl⟩ := hz
    induction hu using AddSubgroup.closure_induction with
    | mem u hu =>
      obtain ⟨α, hα, γ, hγ, rfl⟩ := hu
      refine AddSubgroup.subset_closure ⟨a * α, fun v => GlobalTheory.AdLat.adele_mul_integral F (ha v) (hα v),
        b • γ, Λ.smul_mem b hγ, ?_⟩
      ext i j
      simp only [liftF_tmul, Matrix.smul_apply, smul_eq_mul, ratWF, Matrix.map_apply,
        Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      show (pairA F 0 a ⊗ₜ[F] (b : E)) * ((pairA F 0 α ⊗ₜ[F] (1 : E)) * ((1 : AF F) ⊗ₜ[F] γ i j)) =
        (pairA F 0 (a * α) ⊗ₜ[F] (1 : E)) * ((1 : AF F) ⊗ₜ[F] ((b • γ) i j))
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one, one_mul, one_mul, Matrix.smul_apply]
      congr 1
      exact Prod.ext (mul_zero _) rfl
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | neg x _ hx => rw [smul_neg]; exact neg_mem hx
  | zero => rw [map_zero, zero_smul]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _), add_smul]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg, neg_smul]; exact neg_mem hx

theorem idem_smul_mem {e : AEF F E} (he : e * e = e) (hf : algebraMap (AF F) (AEF F E) (pairA F 0 1) * e = e)
    {u : WOF F E nS nT} (hu : u ∈ latOF F E nS nT Λ) : e • u ∈ latOF F E nS nT Λ := by
  have h1 : finPartF F E e ∈ hatO (F := F) E :=
    GlobalTheory.AdIdem.mem_hat_of_idempotent F E _ (by rw [← map_mul, he])
  rw [← hf, fin_mul_eq]
  exact liftF_smul_mem h1 hu

theorem fin_of_place {e : AEF F E} {α : Af F} (h : algebraMap (AF F) (AEF F E) (pairA F 0 α) * e = e) :
    algebraMap (AF F) (AEF F E) (pairA F 0 1) * e = e := by
  rw [← h, ← mul_assoc, ← map_mul]
  congr 2
  exact Prod.ext (zero_mul _) (one_mul _)

theorem split_parts {e : AEF F E} (he : IsSplitIdemF σ e) :
    (algebraMap (AF F) (AEF F E) (pairA F 0 1) * e = e) ∧
      (algebraMap (AF F) (AEF F E) (pairA F 0 1) * cAF σ e = cAF σ e) ∧ cAF σ e * cAF σ e = cAF σ e := by
  obtain ⟨hee, hec, v, ε, ⟨α, rfl, -⟩, hs⟩ := he
  have hce : cAF σ e * cAF σ e = cAF σ e := by rw [← map_mul, hee]
  refine ⟨fin_of_place (α := α) ?_, fin_of_place (α := α) ?_, hce⟩
  · rw [← hs, add_mul, hee, mul_comm, hec, add_zero]
  · rw [← hs, add_mul, hec, hce, zero_add]

end PositivityTheory.ThKW.LatB

end
end

section -- merged from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Periodic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralCompAut
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

noncomputable section

namespace GlobalTheory.DiagThetaRatF

open MeasureTheory

theorem setIntegral_comp_aut {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G)
    [Countable Γ] {K : Set G} (hK : IsCompact K) (hcov : ∀ x : G, ∃ γ ∈ Γ, γ + x ∈ K) (ν : Measure G)
    [ν.IsAddHaarMeasure] {𝓕 : Set G} (h𝓕 : IsAddFundamentalDomain Γ 𝓕 ν) (e : G ≃+ G) (he : Continuous e)
    (he' : Continuous e.symm) (hΓ : ∀ x ∈ Γ, e x ∈ Γ) (hΓ' : ∀ x ∈ Γ, e.symm x ∈ Γ) (φ : G → ℂ)
    (hφ : ∀ γ ∈ Γ, ∀ x, φ (γ + x) = φ x) : ∫ x in 𝓕, φ (e x) ∂ν = ∫ x in 𝓕, φ x ∂ν := by
  let h : G ≃ₜ G := .mk e.toEquiv he he'
  let m : G ≃ᵐ G := h.toMeasurableEquiv
  haveI : (ν.map e).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map ν e he he'
  have hmp : MeasurePreserving m ν (ν.map e) := ⟨he.measurable, rfl⟩
  have hT : IsAddFundamentalDomain Γ (m.symm ⁻¹' 𝓕) (ν.map e) := by
    refine h𝓕.preimage_of_equiv hmp.symm.quasiMeasurePreserving (e := fun γ : Γ => (⟨e γ, hΓ _ γ.2⟩ : Γ)) ⟨?_, ?_⟩ ?_
    · intro a b hab
      exact Subtype.ext (e.injective (congrArg Subtype.val hab))
    · intro a
      exact ⟨⟨e.symm a, hΓ' _ a.2⟩, Subtype.ext (e.apply_symm_apply _)⟩
    · intro γ x
      show e.symm (e γ + x) = γ + e.symm x
      rw [map_add (f := _), e.symm_apply_apply]
  obtain ⟨c, hc⟩ : ∃ c : NNReal, ν.map e = c • ν := ⟨_, Measure.isAddLeftInvariant_eq_smul _ ν⟩
  have hac : ν.map e ≪ ν := hc ▸ Measure.smul_absolutelyContinuous
  have hF' : IsAddFundamentalDomain Γ 𝓕 (ν.map e) := h𝓕.mono hac
  have hpre : m ⁻¹' (m.symm ⁻¹' 𝓕) = 𝓕 := by
    ext x
    simp
  have h0 : ν 𝓕 ≠ 0 := h𝓕.measure_ne_zero (NeZero.ne ν)
  have h1 : ν 𝓕 ≠ ⊤ := (GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact Γ hK hcov ν h𝓕).ne
  have e1 : ν.map e (m.symm ⁻¹' 𝓕) = ν 𝓕 := by
    have := m.map_apply (μ := ν) (m.symm ⁻¹' 𝓕)
    rw [hpre] at this
    exact this
  have hc1 : (c : ENNReal) = 1 := by
    have e2 := hT.measure_eq hF'
    rw [e1, hc, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at e2
    exact ((ENNReal.mul_left_inj h0 h1).1 ((one_mul _).trans e2)).symm
  have hν : ν.map e = ν := by
    rw [hc, ENNReal.coe_eq_one.1 hc1, one_smul]
  have e3 := hmp.setIntegral_preimage_emb m.measurableEmbedding φ (m.symm ⁻¹' 𝓕)
  rw [hpre] at e3
  refine e3.trans ?_
  rw [hT.setIntegral_eq hF' fun g x => hφ g g.2 x, hν]

section Mat

variable {R : Type} [CommRing R] {m n : ℕ}

end Mat

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem inclR_injective : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
  Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F)

theorem det_ne_zero_of_unit {n : ℕ} (g : GL (Fin n) (AF F ⊗[F] E)) (g₀ : Matrix (Fin n) (Fin n) E)
    (h : g.1 = incM F g₀) : g₀.det ≠ 0 := fun h0 => by
  haveI : Nontrivial (AF F ⊗[F] E) := (inclR_injective (F := F) (E := E)).nontrivial
  have := (Matrix.GeneralLinearGroup.det g).ne_zero
  rw [Matrix.GeneralLinearGroup.val_det_apply, h] at this
  refine this ?_
  have e : (incM F g₀).det = inclR (F := F) (AF F) g₀.det := by
    rw [RingHom.map_det]; rfl
  rw [e, h0, map_zero]

variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}

end Adelic

end GlobalTheory.DiagThetaRatF

end
end

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace PositivityTheory.ThKW.PhaseFourierInjectivity

open PositivityTheory.ThKW.ModulusFactorDefinition

theorem periodic {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E} {ψ : AddChar (AF F) ℂ}
    {f : WOF F E nS (nT + nT) → ℂ} (hf : IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ ψ f) :
    ∀ γ ∈ ratLF F E nS nT, ∀ v : WOF F E nS nT,
      f (dC (AF F ⊗[F] E) nT * (γ + v)) = f (dC (AF F ⊗[F] E) nT * v) := by
  rintro _ ⟨γ, rfl⟩ v
  show f (GlobalTheory.SplitLagrF.dC F E nT * ((ratWF γ : WOF F E nS nT) + v)) = f (GlobalTheory.SplitLagrF.dC F E nT * v)
  have hq := hf.quasi (GlobalTheory.LagrThetaInv.dC E nT * γ) (GlobalTheory.SplitLagrF.dC F E nT * v)
  rw [← GlobalTheory.SplitLagrF.dC_mul_ratWF, GlobalTheory.SplitLagrF.symplOHF_dC, neg_zero, AddChar.map_zero_eq_one, one_mul] at hq
  rw [Matrix.mul_add, hq]

theorem integrable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (ψ : AddChar (AF F) ℂ)
    (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
    ∀ f, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ ψ f →
      Integrable (fun u : WOF F E nS nT => f (dC (AF F ⊗[F] E) nT * u)) (ν.restrict 𝓕) := by
  intro F E _ _ _ _ _ σ nS nT JS JT ξ₀ ψ ν 𝓕 hν h𝓕 f hf
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.T.rationalMatrices_discrete_cocompact_adelicMatrixSpace F E nS nT
  have : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  have : Countable (ratLF F E nS nT) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  have : IsFiniteMeasure (ν.restrict 𝓕) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WOF F E nS nT) (ratLF F E nS nT) hK hKc ν h𝓕⟩
  have hcont : Continuous fun u : WOF F E nS nT => f (dC (AF F ⊗[F] E) nT * u) :=
    hf.cont.comp (continuous_const.matrix_mul continuous_id)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  refine Integrable.of_bound hcont.aestronglyMeasurable C (Filter.Eventually.of_forall fun w => ?_)
  obtain ⟨γ, hγ, h⟩ := hKc w
  rw [← periodic hf γ hγ w]
  exact hC _ h

theorem rat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle) (ωd : GAF σ JS × GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
            Module.End ℂ (WOF F E nS (nT + nT) → ℂ)),
        IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
            (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ γ ∈ GQF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT), ∀ t : GL (Fin nT) (AF F ⊗[F] E),
        mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) γ * dC (AF F ⊗[F] E) nT = dC (AF F ⊗[F] E) nT * t.1 →
      ∀ f, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
        GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT) (ωd (1, γ) f) =
          GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT) f := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ ν 𝓕 hν h𝓕 χS ωd hω γ hγ t ht f hf
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.T.rationalMatrices_discrete_cocompact_adelicMatrixSpace F E nS nT
  have : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  have : Countable (ratLF F E nS nT) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  have h0 : ∀ y : WOF F E nS (nT + nT), symplOHF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ 0 y = 0 := fun y => by
    simp [symplOHF, symplOF, hOF]
  have h1 : ∀ w : WOF F E nS nT, ωd (1, γ) f (dC (AF F ⊗[F] E) nT * w) = f (dC (AF F ⊗[F] E) nT * ((t⁻¹).1 * w)) := by
    intro w
    have hact : actOF σ JS _ 1 γ (dC (AF F ⊗[F] E) nT * ((t⁻¹).1 * w)) = dC (AF F ⊗[F] E) nT * w := by
      unfold actOF
      rw [inv_one, show mtF σ JS 1 = 1 from rfl, Matrix.mul_one, ← Matrix.mul_assoc, ht, Matrix.mul_assoc,
        ← Matrix.mul_assoc t.1, Units.mul_inv, Matrix.one_mul]
    have h2 := congrFun (hω.om_heis 1 γ (dC (AF F ⊗[F] E) nT * ((t⁻¹).1 * w)) f hf) 0
    rw [hω.om_aut 1 (one_mem _) γ hγ _ (GlobalTheory.HeisThetaF.isThetaFunOF_heisOF F E σ B hB _ _ JS _ ξ₀ _ f hf), hact] at h2
    simp only [heisOF, h0, AddChar.map_zero_eq_one, one_mul, zero_add] at h2
    exact h2.symm
  obtain ⟨g₀, -, hg⟩ := hγ
  have hg' : mtF σ _ γ = g₀.1.map (incAF F E) := (congrArg Units.val hg).symm
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : Matrix (Fin nT) (Fin nT) E, t.1 = incM F s₀ := by
    refine ⟨(g₀.1 * GlobalTheory.LagrThetaInv.dC E nT).submatrix (fun p => finSumFinEquiv (Sum.inl p)) id, ?_⟩
    have e : (g₀.1 * GlobalTheory.LagrThetaInv.dC E nT).map (incAF F E) = dC (AF F ⊗[F] E) nT * t.1 := by
      rw [Matrix.map_mul, ← hg', ← ht]
      congr 1
      have := GlobalTheory.LagrThetaInv.dC_mul_rat (F := F) (1 : Matrix (Fin nT) (Fin nT) E)
      rw [Matrix.mul_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at this
      exact this.symm
    ext i j
    rw [← GlobalTheory.LagrThetaInv.dC_mul_inl t.1, ← e]
    rfl
  have hd := GlobalTheory.DiagThetaRatF.det_ne_zero_of_unit t s₀ hs₀
  have hs₁ : (t⁻¹).1 = incM F s₀⁻¹ := by
    rw [Matrix.coe_units_inv]
    refine Matrix.inv_eq_right_inv ?_
    rw [hs₀]
    show s₀.map (inclR (F := F) (AF F)) * s₀⁻¹.map (inclR (F := F) (AF F)) = 1
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hd),
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hm : ∀ (s : Matrix (Fin nT) (Fin nT) E) (x : WOF F E nS nT), x ∈ ratLF F E nS nT →
      (incM F s * x : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)) ∈ ratLF F E nS nT := by
    rintro s _ ⟨y, rfl⟩
    refine ⟨s * y, ?_⟩
    show (s * y).map (incAF F E) = s.map (incAF F E) * y.map (incAF F E)
    exact Matrix.map_mul
  let e : WOF F E nS nT ≃+ WOF F E nS nT :=
    { toFun := fun w => (t⁻¹).1 * w
      invFun := fun w => t.1 * w
      left_inv := fun w => by simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      right_inv := fun w => by simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      map_add' := fun v w => Matrix.mul_add _ v w }
  unfold GlobalTheory.LagrTheta.lagrInt
  simp only [h1]
  exact GlobalTheory.DiagThetaRatF.setIntegral_comp_aut (ratLF F E nS nT) hK hKc ν h𝓕 e
    (continuous_const.matrix_mul continuous_id) (continuous_const.matrix_mul continuous_id)
    (fun x hx => by
      show (t⁻¹).1 * x ∈ _
      rw [hs₁]
      exact hm _ x hx)
    (fun x hx => by
      show t.1 * x ∈ _
      rw [hs₀]
      exact hm _ x hx)
    (fun w => f (dC (AF F ⊗[F] E) nT * w)) (periodic hf)

end PositivityTheory.ThKW.PhaseFourierInjectivity

end
end
