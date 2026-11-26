module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.Assembly
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.SplitDomOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AesmIteratedDerivReal
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSplitting.SplitW
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SiegelSetUnitary

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LowerMulJG
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousLowG
noncomputable section

open Matrix Filter Topology
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.BigCell

open PositivityTheory.Rg.Sw

variable {n : ℕ}

def lowU (t : ℝ) : M2 n := fromBlocks 1 0 ((t : ℂ) • 1) 1

theorem lowU_mul (s t : ℝ) : (lowU s : M2 n) * lowU t = lowU (s + t) := by
  simp [lowU, fromBlocks_multiply, add_smul, add_comm]

theorem lowU_zero : (lowU 0 : M2 n) = 1 := by
  simp [lowU, fromBlocks_one]

theorem lowU_inG (t : ℝ) : InG (lowU t : M2 n) := by
  simp [InG, lowU, JJ, fromBlocks_conjTranspose, fromBlocks_multiply]

def lowG (t : ℝ) : GR n :=
  ⟨⟨lowU t, lowU (-t), by simp [lowU_mul, lowU_zero], by simp [lowU_mul, lowU_zero]⟩, lowU_inG t⟩

theorem lowG_zero : (lowG 0 : GR n) = 1 :=
  Subtype.ext (Units.ext lowU_zero)

theorem continuous_lowU : Continuous (lowU : ℝ → M2 n) := by
  unfold lowU
  exact Continuous.matrix_fromBlocks continuous_const continuous_const
    (Complex.continuous_ofReal.smul continuous_const) continuous_const

theorem continuous_lowG : Continuous (lowG : ℝ → GR n) := by
  have h : Continuous (fun t : ℝ => ((lowG t : GR n) : GL (Fin n ⊕ Fin n) ℂ)) :=
    Units.continuous_iff.2 ⟨(continuous_lowU : Continuous (lowU : ℝ → M2 n)),
      ((continuous_lowU : Continuous (lowU : ℝ → M2 n)).comp continuous_neg)⟩
  exact h.subtype_mk _

theorem JJ_mul_JJ : JJ n * JJ n = -1 := by
  rw [JJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]
  simp

theorem mul_JJ_mul_conj {M : M2 n} (h : InG M) : M * JJ n * Mᴴ = JJ n := by
  have h1 : (JJ n * Mᴴ * JJ n) * M = -1 := by
    calc (JJ n * Mᴴ * JJ n) * M = JJ n * (Mᴴ * JJ n * M) := by simp only [Matrix.mul_assoc]
      _ = -1 := by rw [h, JJ_mul_JJ]
  have h2 : (-(JJ n * Mᴴ * JJ n)) * M = 1 := by rw [Matrix.neg_mul, h1, neg_neg]
  have h3 : M * (-(JJ n * Mᴴ * JJ n)) = 1 := mul_eq_one_comm.1 h2
  calc M * JJ n * Mᴴ = (M * (-(JJ n * Mᴴ * JJ n))) * JJ n := by
        simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, JJ_mul_JJ]
        simp
    _ = JJ n := by rw [h3, Matrix.one_mul]

theorem lower_symm {A B C D : Matrix (Fin n) (Fin n) ℂ} (h : InG (fromBlocks A B C D)) :
    C * Dᴴ = D * Cᴴ := by
  have := congrArg toBlocks₂₂ (mul_JJ_mul_conj h)
  simp [JJ, fromBlocks_multiply, fromBlocks_conjTranspose] at this
  exact (neg_add_eq_zero.1 this).symm

theorem det_lower_I_ne (y : GR n) :
    ((mR y).toBlocks₂₁ + Complex.I • (mR y).toBlocks₂₂).det ≠ 0 := by
  set C := (mR y).toBlocks₂₁ with hC
  set D := (mR y).toBlocks₂₂ with hD
  have hM : InG (fromBlocks (mR y).toBlocks₁₁ (mR y).toBlocks₁₂ C D) := by
    rw [hC, hD, fromBlocks_toBlocks]; exact y.2
  have hs : C * Dᴴ = D * Cᴴ := lower_symm hM
  intro h0
  obtain ⟨v, hv, hvE⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
  have hEE : (C + Complex.I • D) * (C + Complex.I • D)ᴴ = fromCols C D * (fromCols C D)ᴴ := by
    rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromCols_mul_fromRows]
    simp only [conjTranspose_add, conjTranspose_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.smul_mul, Matrix.mul_smul, hs, smul_smul, Complex.star_def, Complex.conj_I]
    simp
    abel_nf
    simp [smul_smul]
  have hL : v ᵥ* fromCols C D = 0 := by
    rw [← Matrix.vecMul_self_mul_conjTranspose_eq_zero, ← hEE, ← Matrix.vecMul_vecMul, hvE,
      Matrix.zero_vecMul]
  have hw : (Sum.elim (0 : Fin n → ℂ) v) ᵥ* mR y = 0 := by
    funext j
    have := congrFun hL j
    rcases j with j | j <;>
      simpa [vecMul, dotProduct, Fintype.sum_sum_type, C, D, toBlocks₂₁, toBlocks₂₂] using this
  have hdet : (mR y).det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero y.1
  have := Matrix.eq_zero_of_vecMul_eq_zero hdet hw
  apply hv
  funext i
  simpa using congrFun this (Sum.inr i)

def detPoly (C D : Matrix (Fin n) (Fin n) ℂ) : Polynomial ℂ :=
  (C.map Polynomial.C + (Polynomial.X : Polynomial ℂ) • D.map Polynomial.C).det

theorem eval_detPoly (C D : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    (detPoly C D).eval z = (C + z • D).det := by
  have := (Polynomial.evalRingHom z).map_det
    (C.map Polynomial.C + (Polynomial.X : Polynomial ℂ) • D.map Polynomial.C)
  rw [detPoly, ← Polynomial.coe_evalRingHom, this]
  congr 1
  ext i j
  simp
  ring

theorem lower_mul_lowG (y : GR n) (t : ℝ) :
    (mR (y * lowG t)).toBlocks₂₁ = (mR y).toBlocks₂₁ + (t : ℂ) • (mR y).toBlocks₂₂ := by
  have h : mR (y * lowG t) = mR y * lowU t := rfl
  rw [h]
  conv_lhs => rw [← fromBlocks_toBlocks (mR y)]
  simp [lowU, fromBlocks_multiply]

theorem dense_bigCell : ∀ n : ℕ, Dense {y : GR n | ((mR y).toBlocks₂₁).det ≠ 0} := by
  intro n y
  have hP : detPoly (mR y).toBlocks₂₁ (mR y).toBlocks₂₂ ≠ 0 := by
    intro h
    apply det_lower_I_ne y
    rw [← eval_detPoly, h, Polynomial.eval_zero]
  have hfin : {t : ℝ | (detPoly (mR y).toBlocks₂₁ (mR y).toBlocks₂₂).eval (t : ℂ) = 0}.Finite :=
    (Polynomial.finite_setOf_isRoot hP).preimage Complex.ofReal_injective.injOn
  have hcl : IsClosed ({t : ℝ | (detPoly (mR y).toBlocks₂₁ (mR y).toBlocks₂₂).eval (t : ℂ) = 0} \ {0}) :=
    (hfin.subset Set.diff_subset).isClosed
  have hnh := hcl.isOpen_compl.mem_nhds (x := (0 : ℝ)) (by simp)
  have ht : Tendsto (fun t : ℝ => y * lowG t) (𝓝[≠] 0) (𝓝 y) := by
    have hc : Continuous (fun t : ℝ => y * lowG t) := continuous_const.mul continuous_lowG
    have := hc.tendsto 0
    simp only [lowG_zero, mul_one] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto ht ?_
  filter_upwards [nhdsWithin_le_nhds hnh, self_mem_nhdsWithin] with t h1 h2
  show ((mR (y * lowG t)).toBlocks₂₁).det ≠ 0
  rw [lower_mul_lowG, ← eval_detPoly]
  intro h3
  exact h1 ⟨h3, h2⟩

end GlobalTheory.CompanionTheory.BigCell
end
end

noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.BigCell

open PositivityTheory.Rg.Sw

variable {n : ℕ}

theorem JJ_inG : InG (JJ n) := by
  have hc : (JJ n)ᴴ = -JJ n := by
    unfold JJ
    simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_neg]
  show (JJ n)ᴴ * JJ n * JJ n = JJ n
  rw [hc, Matrix.mul_assoc, JJ_mul_JJ]
  simp

def JG : GR n :=
  ⟨⟨JJ n, -JJ n, by simp [JJ_mul_JJ], by simp [JJ_mul_JJ]⟩, JJ_inG⟩

theorem lower_mul_JG (y : GR n) :
    (mR (y * JG)).toBlocks₂₁ = -(mR y).toBlocks₂₂ := by
  have h : mR (y * JG) = mR y * JJ n := rfl
  rw [h, ← Matrix.fromBlocks_toBlocks (mR y)]
  unfold JJ
  rw [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂]
  simp

theorem dense_bigCell₂₂ : ∀ n : ℕ, Dense {y : GR n | ((mR y).toBlocks₂₂).det ≠ 0} := by
  intro n
  have hset : {y : GR n | ((mR y).toBlocks₂₂).det ≠ 0} =
      (fun y => y * (JG (n := n))) ⁻¹' {y : GR n | ((mR y).toBlocks₂₁).det ≠ 0} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, lower_mul_JG, Matrix.det_neg]
    constructor
    · intro h
      exact mul_ne_zero (pow_ne_zero _ (by norm_num)) h
    · intro h h0
      exact h (by rw [h0, mul_zero])
  rw [hset]
  exact (dense_bigCell n).preimage (isOpenMap_mul_right _)

end GlobalTheory.CompanionTheory.BigCell
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StripOpenRealDiscs
namespace GlobalTheory.CompanionTheory.Strip

theorem strip_open_real_discs (n : ℕ) (X : Fin n → ℝ) :
    IsOpen {z : ℂ | ∀ j, |z.im * X j| < Real.pi / 4} ∧
    (∀ t : ℝ, (t : ℂ) ∈ {z : ℂ | ∀ j, |z.im * X j| < Real.pi / 4}) ∧
    ∀ z ∈ {z : ℂ | ∀ j, |z.im * X j| < Real.pi / 4}, ∃ (t ρ : ℝ), 0 < ρ ∧
      z ∈ Metric.ball (t : ℂ) ρ ∧
      Metric.ball (t : ℂ) ρ ⊆ {z : ℂ | ∀ j, |z.im * X j| < Real.pi / 4} := by
  set S := {z : ℂ | ∀ j, |z.im * X j| < Real.pi / 4} with hS
  have hpi : 0 < Real.pi / 4 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · have h : S = ⋂ j, {z : ℂ | |z.im * X j| < Real.pi / 4} := by
      ext z
      simp [hS]
    rw [h]
    exact isOpen_iInter_of_finite fun j => isOpen_lt (by fun_prop) continuous_const
  · intro t
    simp [hS, hpi]
  · intro z hz
    have hopen : IsOpen {r : ℝ | ∀ j, r * |X j| < Real.pi / 4} := by
      have h : {r : ℝ | ∀ j, r * |X j| < Real.pi / 4} = ⋂ j, {r : ℝ | r * |X j| < Real.pi / 4} := by
        ext r
        simp
      rw [h]
      exact isOpen_iInter_of_finite fun j => isOpen_lt (by fun_prop) continuous_const
    have hmem : |z.im| ∈ {r : ℝ | ∀ j, r * |X j| < Real.pi / 4} := by
      intro j
      have h := hz j
      rwa [abs_mul] at h
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen _ hmem
    refine ⟨z.re, |z.im| + ε / 2, by positivity, ?_, ?_⟩
    · rw [Metric.mem_ball, Complex.dist_eq]
      have h : z - (z.re : ℂ) = (z.im : ℂ) * Complex.I := by
        apply Complex.ext <;> simp
      rw [h, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      linarith
    · intro w hw j
      rw [Metric.mem_ball, Complex.dist_eq] at hw
      have him : |w.im| < |z.im| + ε / 2 := by
        have h1 : |(w - (z.re : ℂ)).im| ≤ ‖w - (z.re : ℂ)‖ := Complex.abs_im_le_norm _
        simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at h1
        linarith
      have hρ : (|z.im| + ε / 2) * |X j| < Real.pi / 4 := by
        have hin : |z.im| + ε / 2 ∈ Metric.ball |z.im| ε := by
          rw [Metric.mem_ball, Real.dist_eq, show |z.im| + ε / 2 - |z.im| = ε / 2 by ring,
            abs_of_pos (by positivity)]
          linarith
        exact hball hin j
      show |w.im * X j| < Real.pi / 4
      rw [abs_mul]
      calc |w.im| * |X j| ≤ (|z.im| + ε / 2) * |X j| :=
            mul_le_mul_of_nonneg_right him.le (abs_nonneg _)
        _ < Real.pi / 4 := hρ

end GlobalTheory.CompanionTheory.Strip
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CountableOfNumberField
namespace GlobalTheory.CompanionTheory.NumberFieldMatrix

theorem countable_of_numberField (E : Type) [Field E] [NumberField E] : Countable E :=
  (Module.finBasis ℚ E).equivFun.injective.countable

theorem countable_matrix (E : Type) [Field E] [NumberField E] (m n : ℕ) :
    Countable (Matrix (Fin m) (Fin n) E) := by
  haveI := GlobalTheory.CompanionTheory.NumberFieldMatrix.countable_of_numberField E
  exact inferInstanceAs (Countable (Fin m → Fin n → E))

theorem matrix_countable :
    ∀ (E : Type) [Field E] [NumberField E] (m n : ℕ),
      Countable (Matrix (Fin m) (Fin n) E) :=
  fun E _ _ m n => countable_matrix E m n

end GlobalTheory.CompanionTheory.NumberFieldMatrix
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.Bridge
noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Kdil

theorem derCont : DerCont := GlobalTheory.CompanionTheory.HolFamily.continuousOn_iteratedDeriv_family

theorem stripOK : StripOK := GlobalTheory.CompanionTheory.Strip.strip_open_real_discs

theorem matCount : MatCount := GlobalTheory.CompanionTheory.NumberFieldMatrix.matrix_countable

theorem holMean : HolMean := GlobalTheory.CompanionTheory.HolMean.holomorphic_mean

theorem bigDense : BigDense := GlobalTheory.CompanionTheory.BigCell.dense_bigCell₂₂

end PositivityTheory.SiegelWeilFormula.Kdil

end
end

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Kdil

theorem decompW : DecompW := fun _ _ _ _ _ _ _ _ d R w g => KSplitW.decompW d R w g

theorem gIdil (hT : TAll) (hAux : AuxiliaryPrimeFunction) (hLE : LocOpEx) (hAw : AwayAct) (hS : GlobalTheory.Published.SiegelSetUnitary)
    (hLF : LocFamG) (hBD : BigDense) : GIdil :=
  gIdil_of hT hAux hLE (thetaPt_of hT) (fun _ _ P => KFock.isSw_fP P) matCount (splitDom_of hT hAw decompW)
    (thetaBdd_of hS) hLF hBD holMean derCont stripOK

theorem gIdil' (hT : TAll) (hAux : AuxiliaryPrimeFunction) (hLE : LocOpEx) (hAw : AwayAct) (hLF : LocFamG) : GIdil :=
  gIdil hT hAux hLE hAw GlobalTheory.T.siegel_set_unitary hLF bigDense

end PositivityTheory.SiegelWeilFormula.Kdil

end
