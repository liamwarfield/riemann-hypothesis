module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaBasicK
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaIntegralUnfolding
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.DoubledLagrangianInvariantFunctional
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitHermOfDet
public import Development.WeilBound.ThetaLifts.LatticeBasics.FinLevel
public import Development.WeilBound.ThetaLifts.LatticeBasics.FrameB
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightContinuousPosStatement

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.BaseKnownTheoremsE
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
def SiegelWeilAniso_k : Prop := _root_.GlobalTheory.ThK.Dbl.SWAniso_k ∧ _root_.GlobalTheory.ThK.Dbl.SWAnisoX_k
def EisBL_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, _root_.UpperTheory.TP.W.GoodK σ B → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) →
    ∀ χ : Chr F E, IsHecke F E χ → ∀ c : ℕ, ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ c →
    ∀ b K a, IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → ∀ s₁ f, IsSec K χ s₁ f →
      ∃ Ê : ℂ → G2 σ Y → ℂ, (∃ t : ℝ, (∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) (Ê s x)) ∧
          ∀ x, DifferentiableOn ℂ (Ê · x) {s | t < s.re}) ∧
        ∀ s₀, ∃ (k : ℕ) (U : Set ℂ) (H : ℂ → modFun σ Y), U ∈ 𝓝 s₀ ∧ (∀ s ∈ U, s ≠ s₀ → ∀ x, (H s).1 x = (s - s₀) ^ k * Ê s x) ∧
          ∀ μ, IsGrowForm μ → DifferentiableOn ℂ (fun s => μ (H s)) U
def FrameConj_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, _root_.UpperTheory.TP.W.GoodK σ B → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) →
    ∀ K, IsStab2 (σ := σ) (Y := Y) B K → ∃ b K₀ p t, IsFrame2 σ Y b ∧ IsStdK B b K₀ ∧ IsPar p t ∧ ∀ k, k ∈ K ↔ p⁻¹ * k * p ∈ K₀
end GlobalTheory.ThK.Dbl
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.StandardAdditiveCharacterSign
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_additive_character_sign : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) := by
  first | exact @_root_.GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood_k | exact _root_.GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood_k | (intros; apply _root_.GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood_k <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkEstStmt
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace PositivityTheory.ThKEst
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
section Pair
variable {n d : ℕ}
variable {X : Spc F E n} {W : Spc F E d}
end Pair
def EpsOf_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∀ (n : ℕ) (X : Spc F E n) (r s : ℕ), (X.IsHerm σ B r s ∨ X.IsSkew σ B r s) → EpsHerm σ X.J ∧ r + s = n ∧ ∀ fr : Frame σ X.J, fr.IsGood → fr.r ≤ min r s
def CoefEq_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) χX χW om r s r' s', _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s' → ∀ μ : Measure (Fin n × Fin d → AF F), μ.IsAddHaarMeasure → ∀ Φ₁ ∈ schA F (Fin n × Fin d), ∀ Φ₂ ∈ schA F (Fin n × Fin d), ∀ (g : UA σ X.J) (h : UA σ W.J) (z : Ten F E n d), coef F B.ψ μ (om (g, h) Φ₁) (om (g, h) Φ₂) (M.co.e z) = coef F B.ψ μ Φ₁ Φ₂ (M.co.e (mat g⁻¹ * z * (mat h⁻¹)ᵀ))
def CoefBd_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) χX χW om r s r' s', _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s' → ∀ μ : Measure (Fin n × Fin d → AF F), μ.IsAddHaarMeasure → ∀ φ₁ ∈ SB (Fin n × Fin d → Af F), ∀ φ₂ ∈ SB (Fin n × Fin d → Af F), ∀ N : ℕ, ∃ (p : Seminorm ℂ (SInf F (Fin n × Fin d))) (C : Set (Ten F E n d)), Continuous p ∧ IsCompact C ∧ ∀ (f₁ f₂ : SInf F (Fin n × Fin d)) (z : Ten F E n d), ‖coef F B.ψ μ (pureA F f₁ φ₁) (pureA F f₂ φ₂) (M.co.e z)‖ ≤ p f₁ * p f₂ * maj B.emb C N z
end PositivityTheory.ThKEst
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkTowStmt
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace PositivityTheory.ThKG.Tow
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
def ModelEx_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → W.IsSkew σ B r' s' → ∃ M : Model σ X W, M.IsGood B.ψ
def WeilEx_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → W.IsSkew σ B r' s' → ∀ M : Model σ X W, M.IsGood B.ψ →
    ∀ χX χW : Chr F E, IsHecke F E χX → IsHecke F E χW →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → ∃ om, M.IsWeil B.ψ χX χW om
def PairEx_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → W.IsSkew σ B r' s' → (∃ M : Model σ X W, M.IsGood B.ψ) ∧
    ∀ χX χW : Chr F E, IsHecke F E χX → IsHecke F E χW →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d →
      ∀ M : Model σ X W, M.IsGood B.ψ → ∃ om, _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s'
theorem pairEx_of_k (h₁ : _root_.PositivityTheory.ThKG.Tow.ModelEx_k) (h₂ : _root_.PositivityTheory.ThKG.Tow.WeilEx_k) : _root_.PositivityTheory.ThKG.Tow.PairEx_k := by
  intro F E _ _ _ _ _ σ B hB n d X W r s r' s' hX hW
  refine ⟨h₁ F E σ B hB n d X W r s r' s' hX hW, fun χX χW a b c e M hM => ?_⟩
  obtain ⟨om, hom⟩ := h₂ F E σ B hB n d X W r s r' s' hX hW M hM χX χW a b c e
  exact ⟨om, hB, hX, hW, hM, a, b, c, e, hom⟩
end PositivityTheory.ThKG.Tow
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaFunctionHeisenbergTranslate
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_function_heisenberg_translate : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E)
      (w₀ : WOF F E nS nT) (f : WOF F E nS nT → ℂ), IsThetaFunOF σ JS JT ξ₀ B.ψ f →
        IsThetaFunOF σ JS JT ξ₀ B.ψ (heisOF σ JS JT ξ₀ B.ψ w₀ f) := by
  first | exact @_root_.GlobalTheory.HeisThetaF.isThetaFunOF_heisOF_k | exact _root_.GlobalTheory.HeisThetaF.isThetaFunOF_heisOF_k | (intros; apply _root_.GlobalTheory.HeisThetaF.isThetaFunOF_heisOF_k <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EisensteinSeriesConvergenceBound
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_series_convergence_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), _root_.UpperTheory.TP.W.GoodK σ B → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → ∃ σ₀ : ℝ, ∀ σ' : ℝ, σ₀ < σ' → ∃ (C : ℝ) (N : ℕ), ∀ x : G2 σ Y, Summable (fun q : Cos σ Y => a ((Quotient.out q).1 * x) ^ σ') ∧ ∑' q : Cos σ Y, a ((Quotient.out q).1 * x) ^ σ' ≤ C * (ht2 x : ℝ) ^ N := by
  first | exact @_root_.GlobalTheory.CompanionTheory.GodementH.godement_sum_k | exact _root_.GlobalTheory.CompanionTheory.GodementH.godement_sum_k | (intros; apply _root_.GlobalTheory.CompanionTheory.GodementH.godement_sum_k <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseStmtN
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
def PolSch_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s' → ∀ Φ ∈ PolData B M, Φ ∈ schA F _
end GlobalTheory.ThK.Dbl
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkFacStmt
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace PositivityTheory.ThKF
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}
def ArchOp_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s' →
    ∀ g ∈ UAt σ X (evI F), ∀ h ∈ UAt σ W (evI F), ∃ T, IsArchOp om (g, h) T ∧
      (g ∈ KInf σ X B.emb → h ∈ KInf σ W B.emb → ∀ f ∈ M.Pol B.ψ B.emb, T f ∈ M.Pol B.ψ B.emb)
end PositivityTheory.ThKF
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.DoubledLagrangianEquivariant
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubled_lagrangian_equivariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ Φ ∈ schA F κ, Continuous (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) := by
  first | exact @_root_.GlobalTheory.ThetaTrContF.continuous_thetaTrF_k | exact _root_.GlobalTheory.ThetaTrContF.continuous_thetaTrF_k | (intros; apply _root_.GlobalTheory.ThetaTrContF.continuous_thetaTrF_k <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.DoubledLagrangianContinuous
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubled_lagrangian_continuous : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ Φ ∈ schA F κ, ∀ (γ : Matrix (Fin nT) (Fin nS) E) (w : WOF F E nS nT),
            GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ (ratWF γ + w) = B.ψ (-(symplOHF σ JS JT ξ₀ (ratWF γ) w)) * GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ w := by
  first | exact @_root_.GlobalTheory.ThetaQuasiRatF.thetaTr_ratWF_add_k | exact _root_.GlobalTheory.ThetaQuasiRatF.thetaTr_ratWF_add_k | (intros; apply _root_.GlobalTheory.ThetaQuasiRatF.thetaTr_ratWF_add_k <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.DoubledLagrangianUnitary
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubled_lagrangian_unitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ Φ ∈ schA F κ, ∃ U : AddSubgroup (WOF F E nS nT), IsOpen (U : Set (WOF F E nS nT)) ∧
            ∀ u ∈ U, u.map (infPartF F E) = 0 → heisOF σ JS JT ξ₀ B.ψ u (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) = GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ := by
  first | exact @_root_.GlobalTheory.ThetaLevelF.thetaTr_levelF_k | exact _root_.GlobalTheory.ThetaLevelF.thetaTr_levelF_k | (intros; apply _root_.GlobalTheory.ThetaLevelF.thetaTr_levelF_k <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SplitModelK
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {m n : ℕ}
variable {Y : Spc F E n} {A : Spc F E m}
attribute [local instance] GlobalTheory.LocalData.complRel
local instance  (v : Pl F) : IsNonarchimedeanLocalField (Fv F v) := GlobalTheory.LocalData.isLocalField v
def SplitModel_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s' → ∀ (v : Pl F) (t : E →ₐ[F] Fv F v), (∃ ι, M.IsLinW B.ψ t 1 1 ι) ∧ ∀ ι, M.IsLinW B.ψ t 1 1 ι →
      ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ (g₀ : GL (Fin n) (Fv F v)) (h₀ : GL (Fin d) (Fv F v)),
        g₀.1 = (mat g).map (piW t) → h₀.1 = (mat h).map (piW t) → ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _, Acts (evFin F v) (om (g, h)) φ φ₁ →
          ι φ₁ = GlobalTheory.SplitFlip.omA (chrW χW t)⁻¹ (chrW χX t) g₀ h₀ (ι φ)
end GlobalTheory.ThK.Dbl
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.HeightFunctionContinuousPos
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.HeightContinuousPosK
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
noncomputable section
namespace GlobalTheory.CompanionTheory.Iwasawa
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
theorem height_continuous_pos_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), _root_.UpperTheory.TP.W.GoodK σ B → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → Continuous a ∧ ∀ x, 0 < a x :=
  fun F E _ _ _ _ _ σ B n Y r s hB hn hY b K a hb hK ha =>
    continuous_pos (_root_.GlobalTheory.T.isCompact_standard_maximal_compact F E σ B n Y r s hB hn hY b K a hb hK ha) ha
end GlobalTheory.CompanionTheory.Iwasawa
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_function_continuous_pos : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), _root_.UpperTheory.TP.W.GoodK σ B → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → Continuous a ∧ ∀ x, 0 < a x := by
  first | exact @_root_.GlobalTheory.CompanionTheory.Iwasawa.height_continuous_pos_k | exact _root_.GlobalTheory.CompanionTheory.Iwasawa.height_continuous_pos_k | (intros; apply _root_.GlobalTheory.CompanionTheory.Iwasawa.height_continuous_pos_k <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Unfold0K
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
variable {χ : Chr F E} {z : ℂ} {f : G2 σ Y → ℂ} {e : UA σ Y.J × UA σ Y.J →* G2 σ Y}
theorem unfold0_k : _root_.GlobalTheory.ThK.Dbl.Unfold0_k := by
  intro F E _ _ _ _ _ σ B n Y r s hB hY h0 χ e hχ he f Ê z _ _ hs hf μ D hμ hD hi φ hφ h
  have hJ := _root_.GlobalTheory.ThK.Dbl.aniso_of_k hB hY h0
  haveI := countable_ratU (σ := σ) (Y := Y)
  haveI : BorelSpace (UA σ Y.J) := ⟨rfl⟩
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  obtain ⟨C, hC⟩ := hφ.2.2 0
  let k : UA σ Y.J → ℂ := fun g => f (e (1, g)) * (detInv χ g * φ (h * g))
  have ik : Integrable k μ := hi.mul_bdd (c := C)
    ((continuous_detInv hχ).mul (hφ.1.comp (continuous_const_mul h))).aestronglyMeasurable
    (.of_forall fun g => by simpa [norm_detInv] using hC (h * g))
  have := An.unfold hD (ik.comp_mul_left h⁻¹)
  rw [integral_mul_left_eq_self k] at this
  simp only [mul_assoc]
  refine Eq.trans (integral_congr_ae (.of_forall fun g => ?_)) this
  refine (((Law.hasSum hf hχ hJ he (hs _)).mul_right _).tsum_eq.symm).trans (tsum_congr fun δ => ?_)
  simp only [k]
  rw [← Law.diag hf hJ he h (e _), ← map_mul, ← map_mul, detInv_mul, detInv_mul, detInv_rat hχ δ.2, mul_inv_cancel_left, hφ.2.1 _ δ.2]
  have : detInv χ h * detInv χ h⁻¹ = 1 := by rw [← detInv_mul, mul_inv_cancel, detInv_rat hχ (one_mem _)]
  simp only [Prod.mk_mul_mk, one_mul, mul_one, mul_inv_cancel_left]
  linear_combination (-(f (e (h, δ * g)) * detInv χ g * φ g)) * this
end GlobalTheory.ThK.Dbl
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseFinLevel
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GroundTheory.Automorphic.GJMatrix GroundTheory.Global GlobalTheory.HeisSchA
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ}
theorem finLevel_k : _root_.GlobalTheory.ThK.Dbl.FinLevel_k := by
  intro F E _ _ _ _ _ σ B m n A Y hB κ _ dd K hK Φ hΦ
  have lin : ∀ (k : G2 σ Y) (u : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)),
      actB (cA σ) k (epsF F • u) = epsF F • actB (cA σ) k u := fun k u => Matrix.smul_mul _ _ _
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : ∀ {α β : Type} [Finite α] [Finite β], IsModuleTopology (AF F) (Matrix α β (AE F E)) :=
    inferInstanceAs (IsModuleTopology (AF F) (_ → _ → AE F E))
  have c : Continuous fun y : ((κ → AF F) × (κ → AF F)) × G2 σ Y => dd.e (actB (cA σ) y.2 (dd.e.symm y.1)) :=
    (IsModuleTopology.continuous_of_linearMap dd.e.toLinearMap).comp
      (((IsModuleTopology.continuous_of_linearMap dd.e.symm.toLinearMap).comp continuous_fst).matrix_mul
        (Units.continuous_val.comp (continuous_subtype_val.comp continuous_snd)).matrix_transpose)
  obtain ⟨s, hs, h⟩ := finite_values hB.std (hK.eventually_forall_of_forall_eventually
    (P := fun w k => schr B.ψ (epsF F • dd.e (actB (cA σ) k (dd.e.symm w))) Φ = Φ) fun k _ =>
      (c.tendsto' (0, k) 0 (by simp [actB])).eventually (level hB.std.1 hΦ))
  refine ⟨{u | epsF F • u = u ∧ ∀ k ∈ K, dd.rho B.ψ (actB (cA σ) k u) Φ = Φ}, fun u hu => ⟨fun i => ?_, fun i => ?_,
    fun k hk => ⟨by rw [← lin, hu.1], fun k' hk' => ?_⟩⟩, fun u hu => ?_, s, hs, fun Ψ hΨ => h Ψ fun w hw => ?_⟩
  · rw [← hu.1, map_smul]; exact evI_epsF _
  · rw [← hu.1, map_smul]; exact evI_epsF _
  · have := hu.2 _ (mul_mem hk' hk)
    simpa [actB, Matrix.mul_assoc] using this
  · simpa [actB] using hu.2 1 (one_mem _)
  · have := hΨ (epsF F • dd.e.symm w) ⟨by rw [smul_smul, epsF_sq], fun k hk => by
      rw [lin, Darboux.rho, map_smul]; exact hw k hk⟩
    rwa [Darboux.rho, map_smul, LinearEquiv.apply_symm_apply] at this
end GlobalTheory.ThK.Dbl
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseStmtX
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {m n : ℕ}
variable {Y : Spc F E n} {A : Spc F E m}
def DblX_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s' → ∃ dd om₂ S l, IsDbl (σ := σ) (A := W) (Y := X) (κ := (Fin n × Fin d) ⊕ (Fin n × Fin d)) B.ψ dd χW om₂ S l ∧
      (∀ Φ₁ ∈ schA F _, ∀ Φ₂ ∈ schA F _, boxFun Φ₁ (star Φ₂) ∈ schA F _ ∧ ∀ h g g' x, IsEmb g g' x →
        detInv χW g' * thetaSum F (om₂ x (S h (boxFun Φ₁ (star Φ₂)))) = theta om Φ₁ g h * star (theta om Φ₂ g' h) ∧
        detInv χW g' • om₂ x (boxFun Φ₁ (star Φ₂)) = boxFun (om (g, 1) Φ₁) (star (om (g', 1) Φ₂))) ∧
      IsDblCoordX M dd ∧
      ∀ ν : @Measure (Fin n × Fin d → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν → ∃ c' : ℝ, 0 < c' ∧
        ∀ Ψ₁ ∈ schA F _, ∀ Ψ₂ ∈ schA F _, l (boxFun Ψ₁ (star Ψ₂)) = c' * ∫ u, Ψ₁ u * star (Ψ₂ u) ∂ν
def BoxSecX_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) r s r' s', _root_.UpperTheory.TP.W.GoodK σ B → 1 ≤ n → 1 ≤ d → X.IsHerm σ B r s →
    W.IsSkew σ B r' s' → min r' s' = 0 → M.IsGood B.ψ →
    ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ d →
    ∀ dd om S l, IsDblCoordX M dd → IsDbl (σ := σ) (A := W) (Y := X) B.ψ dd χ om S l →
    ∀ K a, IsStab2 B K → IsHgt K a →
    ∀ Φ₁ ∈ PolData B M, ∀ Φ₂ ∈ PolData B M, IsSec K χ (((d : ℂ) - n) / 2) (fun x => l (om x (boxFun Φ₁ (star Φ₂))))
def SWFullX_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) r s r' s', _root_.UpperTheory.TP.W.GoodK σ B → 1 ≤ n → 1 ≤ d → X.IsHerm σ B r s →
    W.IsSkew σ B r' s' → min r' s' = 0 → M.IsGood B.ψ →
    ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ d →
    ∀ dd om S l, IsDblCoordX M dd → IsDbl (σ := σ) (A := W) (Y := X) B.ψ dd χ om S l →
    ∀ K a, IsStab2 B K → IsHgt K a →
    ∀ (μ : Measure (UA σ W.J)) (D : Set (UA σ W.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ W.J) D μ →
    ∀ Φ₁ ∈ PolData B M, ∀ Φ₂ ∈ PolData B M,
      ∃ U Ê, IsEisCont (flat a (fun x => l (om x (boxFun Φ₁ (star Φ₂)))) (((d : ℂ) - n) / 2)) U Ê ∧ (((d : ℂ) - n) / 2) ∈ U ∧
        ∀ x, Ê (((d : ℂ) - n) / 2) x = (if n < d then 1 else 2) * ⨍ h in D, thetaSum F (om x (S h (boxFun Φ₁ (star Φ₂)))) ∂μ
end GlobalTheory.ThK.Dbl
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ArchimedeanChartThetaEquivariant
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.PsiSymplOHFIotaVFK
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical
noncomputable section
namespace GlobalTheory.RealCharF
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem psi_symplOHF_iotaVF_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∀ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι →
      ∀ u v : IxF F nS nT → ℂ, B.ψ (symplOHF σ JS JT ξ₀ (iotaVF ι u) (iotaVF ι v)) =
        Complex.exp (Real.pi * Complex.I * ((star v ⬝ᵥ HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1) *ᵥ u).im : ℂ)) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ θ hθ ι hι u v
  have hσ := hB.cm
  haveI : IsTotallyReal F := hσ.1
  have hψ := _root_.GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood_k F E σ B hB
  have hw : ∀ w : InfinitePlace F, w.embedding = (B.emb w).1.comp (algebraMap F E) := fun w => (B.emb w).2.symm
  set s := symplOHF σ JS JT ξ₀ (iotaVF ι u) (iotaVF ι v) with hs
  have hsnd : sndA F s = 0 :=
    GlobalTheory.HeisDerivCM.map_symplOHF_eq_zero (sndA F) σ JS JT ξ₀ _ _ (Or.inr (real_iotaVF hι v))
  have e1 : B.ψ s = psiInf F B.ψ (fstA F s) := by
    have hsplit : s = pairA F (fstA F s) 0 := Prod.ext rfl hsnd
    conv_lhs => rw [hsplit]
    rfl
  have hre : ∀ w : InfinitePlace F, ((B.emb w).1 ξ₀).re = 0 := by
    intro w
    have h1 := hσ.2.2.2 (B.emb w).1 ξ₀
    rw [hσξ, map_neg] at h1
    have h2 := congrArg Complex.re h1
    rw [Complex.neg_re, Complex.star_def, Complex.conj_re] at h2
    linarith
  rw [e1, hψ.2.2 θ hθ, trace_HMF]
  have e2 : ∑ w, θ w (fstA F s ⊗ₜ[F] (1 : E)) = ∑ w, ((((B.emb w).1 ξ₀) *
      ((JS.map (B.emb w).1)⁻¹ * (cpt v w)ᴴ * JT.map (B.emb w).1 * cpt u w).trace).re : ℂ) :=
    Finset.sum_congr rfl fun w _ => by
      rw [hs, theta_fstA_symplOHF hσ (hw w) (hθ w) JS JT ξ₀ (iotaVF ι u) (iotaVF ι v),
        theta_hOF hσ hw hθ hι JT hJS.2 u v]
  rw [e2]
  congr 1
  rw [Complex.im_sum]
  simp only [Complex.mul_re, hre, Complex.im_ofReal_mul, zero_mul, zero_sub]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  ring
end GlobalTheory.RealCharF
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_chart_theta_equivariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∀ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι →
      ∀ u v : IxF F nS nT → ℂ, B.ψ (symplOHF σ JS JT ξ₀ (iotaVF ι u) (iotaVF ι v)) =
        Complex.exp (Real.pi * Complex.I * ((star v ⬝ᵥ HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1) *ᵥ u).im : ℂ)) := by
  first | exact @_root_.GlobalTheory.RealCharF.psi_symplOHF_iotaVF_k | exact _root_.GlobalTheory.RealCharF.psi_symplOHF_iotaVF_k | (intros; apply _root_.GlobalTheory.RealCharF.psi_symplOHF_iotaVF_k <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RationalLatticeSelfDual
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.AdeleRatOfIsGoodK
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace GlobalTheory.RatAnnihF
section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem adele_rat_of_isGood_k {σ : E →ₐ[F] E} {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) (a : AF F)
    (h : ∀ c : F, B.ψ (a * algebraMap F _ c) = 1) : ∃ d : F, a = algebraMap F _ d := by
  haveI : IsTotallyReal F := hB.cm.1
  obtain ⟨⟨θ, hθ⟩, -⟩ := (_root_.GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood_k F E σ B hB).2
  let L : Ainf F →+ ℂ := AddMonoidHom.mk' (fun x => ∑ w, θ w (x ⊗ₜ[F] (1 : E))) fun a b => by
    simp only [map_add (f := _), TensorProduct.add_tmul, Finset.sum_add_distrib]
  have hL : ∀ x, L x = ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F x) : ℝ) : ℂ) :=
    fun x => GlobalTheory.StdCharWeilDatum.sum_infFam B θ hθ x
  refine GlobalTheory.RatAnnih.adele_rat (GlobalTheory.StdCharWeilDatum.isCharAF hB.std) (psiV_exists_ne_one hB.std) L
    (continuous_finsetSum _ fun w _ => (hθ w).2) (fun x => ?_) (fun x => ?_) a h
  · rw [hL]
    have e : InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (Ainf F) x) = mixedEmbedding F x := by
      rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
    rw [e, GlobalTheory.LatVacArith.trace_mixedEmbedding]
    exact Complex.ofReal_ratCast _
  · show B.ψ (pairA F x 0) = _
    rw [GlobalTheory.StdCharWeilDatum.psi_pairA hB.std, hL]
    congr 1
    ring
end
theorem ratLF_annihilator_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
    IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → ∀ x : WOF F E nS nT,
      (∀ γ ∈ ratLF F E nS nT, B.ψ (symplOF σ JS JT ξ₀ x γ) = 1) ↔ x ∈ ratLF F E nS nT := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ x
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hB.cm.2.2.1]; norm_num)
  have hσ : Function.Surjective σ := (Algebra.IsAlgebraic.algHom_bijective σ).2
  constructor
  · intro h
    have hent : ∀ i j, ∃ e : E, x i j = (1 : AF F) ⊗ₜ[F] e := fun i j =>
      GlobalTheory.RatAnnih.tensor_rat (x i j) fun e => _root_.GlobalTheory.RatAnnihF.adele_rat_of_isGood_k hB _ fun c => by
        obtain ⟨γ, hγ, hγe⟩ := exists_symplOF_eq σ hσ hS hT hξ x i j (c • e)
        exact (congrArg B.ψ ((GlobalTheory.RatAnnih.trace_mul_algebraMap (x i j) e c).trans hγe.symm)).trans (h γ hγ)
    choose M hM using hent
    refine ⟨Matrix.of M, Matrix.ext fun i j => ?_⟩
    rw [hM i j]
    rfl
  · rintro ⟨M, rfl⟩ _ ⟨N, rfl⟩
    obtain ⟨a, ha⟩ := symplOF_rat σ JS JT ξ₀ M N
    rw [ha]
    exact (GlobalTheory.StdCharWeilDatum.isCharAF hB.std).2.2.1 a
end GlobalTheory.RatAnnihF
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_lattice_self_dual : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
    IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → ∀ x : WOF F E nS nT,
      (∀ γ ∈ ratLF F E nS nT, B.ψ (symplOF σ JS JT ξ₀ x γ) = 1) ↔ x ∈ ratLF F E nS nT := by
  first | exact @_root_.GlobalTheory.RatAnnihF.ratLF_annihilator_k | exact _root_.GlobalTheory.RatAnnihF.ratLF_annihilator_k | (intros; apply _root_.GlobalTheory.RatAnnihF.ratLF_annihilator_k <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ItemsThkhLocrep
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace PositivityTheory.ThKH.Locrep
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain Filter Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK
open GlobalTheory.EmbChart (atPlace evFin_atPlace atPlace_mul_right)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
theorem locRepEx_k : _root_.PositivityTheory.ThK.LocRepEx_k := by
  intro F E _ _ _ _ _ σ n d B X W M om hP v
  obtain ⟨χX, χW, hw⟩ := hP.weil
  have hs := IsUWeilPair.isUSplitting hw
  have hstd := hP.base.std
  have hne : B.ψ ≠ 1 := fun h => GlobalTheory.PsiNontriv.psiV_ne_one B.ψ hstd v (by rw [h]; rfl)
  have hH := (GlobalTheory.CompanionTheory.AdelicHeis.schr_mem_and_thetaSum F (Fin n × Fin d) B.ψ hstd.1 hne hstd.2.1).1
  obtain ⟨r₀, x₀, h₀, h₁⟩ := exists_base (Fin n × Fin d) v
  let loc : Module.End ℂ ((Fin n × Fin d → AF F) → ℂ) → Module.End ℂ (Fn F n d v) := fun T =>
    res v x₀ ∘ₗ T ∘ₗ tensL v r₀
  have hloc : ∀ T φ, loc T φ = res v x₀ (T (tens (evFin F v) φ r₀)) := fun _ _ => rfl
  have pres : ∀ p, ∀ φ ∈ SB _, loc (om p) φ ∈ SB _ := fun p φ hφ => res_mem v x₀ (hs.pres p _ (h₀ φ hφ).2)
  have presH : ∀ u, ∀ φ ∈ SB _, loc (schrL B.ψ (M.co.e u)) φ ∈ SB _ := fun u φ hφ => res_mem v x₀ (hH _ _ (h₀ φ hφ).2)
  have acts : ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB _,
      Acts (evFin F v) (om (g, h)) φ (loc (om (g, h)) φ) := by
    intro g hg h hh φ hφ
    refine acts_res v hstd.1 hne hstd.2.1 (hs.pres _) (hs.adm _) (fun w h1 h2 Φ hΦ => ?_) h₁ hφ (h₀ φ hφ)
    obtain ⟨u, rfl⟩ := M.co.e.surjective w
    have hu : atPlace v (1 : Fv F v) • u = 0 := by
      apply M.co.e.injective
      rw [map_smul, map_zero]
      refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
      · change atPlace v 1 * (M.co.e u).1 i = 0
        rw [atPlace_mul_right, show evFin F v ((M.co.e u).1 i) = 0 from congrFun h1 i, mul_zero, map_zero]
      · change atPlace v 1 * (M.co.e u).2 i = 0
        rw [atPlace_mul_right, show evFin F v ((M.co.e u).2 i) = 0 from congrFun h2 i, mul_zero, map_zero]
    have := hs.impl (g, h) u Φ hΦ
    rwa [show actAB (cA σ) (g, h) u = u from act_away hg hh hu] at this
  have actsH : ∀ u, At (evFin F v) u → ∀ φ ∈ SB _,
      Acts (evFin F v) (M.co.rho B.ψ u) φ (loc (schrL B.ψ (M.co.e u)) φ) := by
    intro u hu φ hφ
    have e : ∀ a, evFin F v a = 0 → a • M.co.e u = 0 := fun a ha => by rw [← map_smul, hu a ha, map_zero]
    have A : Acts (evFin F v) (M.co.rho B.ψ u) φ _ := fun r hr =>
      GlobalTheory.SchrLoc.schr_tens_of_at B.ψ v (M.co.e u) (fun i a ha => congrFun (congrArg Prod.fst (e a ha)) i)
        (fun i a ha => congrFun (congrArg Prod.snd (e a ha)) i) φ r hr.1
    have := eq_of_acts v h₁ (h₀ φ hφ) A
    rw [this] at A
    exact A
  have one : ∀ φ ∈ SB _, loc (om 1) φ = φ := fun φ hφ =>
    (eq_of_acts v h₁ (h₀ φ hφ) (T := om 1) fun r _ => by rw [map_one]; rfl).symm
  have mul : ∀ p : UA σ X.J × UA σ W.J, ∀ g' ∈ UAt σ X (evFin F v), ∀ h' ∈ UAt σ W (evFin F v), ∀ φ ∈ SB _,
      loc (om (p * (g', h'))) φ = loc (om p) (loc (om (g', h')) φ) := fun p g' hg' h' hh' φ hφ => by
    rw [hloc, hloc (om p), ← acts g' hg' h' hh' φ hφ r₀ (h₀ φ hφ), map_mul]
    rfl
  refine ⟨fun p => loc (om p), fun u => loc (schrL B.ψ (M.co.e u)), fun g _ h _ => pres _,
    fun g hg h hh φ hφ φ₁ => ⟨fun A => eq_of_acts v h₁ (h₀ φ hφ) A, fun e => e ▸ acts g hg h hh φ hφ⟩, one,
    fun g _ h _ => mul (g, h), fun φ hφ => ?_, fun u _ => presH u,
    fun u hu φ hφ φ₁ => ⟨fun A => eq_of_acts v h₁ (h₀ φ hφ) A, fun e => e ▸ actsH u hu φ hφ⟩,
    fun g hg h hh u hu φ hφ => ?_⟩
  · obtain ⟨K, hK1, hK2, hK3, hK4⟩ := exists_small_subgroups σ W v
    obtain ⟨m, hm⟩ := smooth_of_weak (SB _) K hK1 hK2 (fun h => loc (om (1, h))) (fun h _ => pres _) one
      (fun h _ h' hh' φ hφ => by
        have := mul (1, h) 1 (one_mem_UAt X v) h' (hK3 0 hh') φ hφ
        rwa [Prod.mk_mul_mk, one_mul] at this)
      (fun l φ hφ => (hs.cont _ (res_adm v x₀ l) _ (h₀ φ hφ).2).comp (continuous_const.prodMk continuous_id)) φ hφ
    obtain ⟨U, hU, hUK⟩ := hK4 m
    exact ⟨U, hU, fun h hh hv => hm h (hUK h hh hv)⟩
  · change loc (om (g, h)) (loc (schrL B.ψ (M.co.e u)) φ) = loc (schrL B.ψ (M.co.e _)) (loc (om (g, h)) φ)
    rw [hloc (om (g, h)), hloc _ (loc (om (g, h)) φ), ← actsH u hu φ hφ r₀ (h₀ φ hφ),
      ← acts g hg h hh φ hφ r₀ (h₀ φ hφ), hs.impl _ _ _ (h₀ φ hφ).2]
    rfl
end PositivityTheory.ThKH.Locrep
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseFrameB
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl.Frame
open scoped Matrix TensorProduct
open NumberField IsDedekindDomain Filter GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.InertChart GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Doubling
open PositivityTheory.ThKH.Iwas Hgt
open Formalism.UG (bc)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {v : Pl F}
theorem inD_mem_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {w : Pl E} (hw : Formalism.UG.IsInertAt F E v w) {z : E} (hz : InD z) :
    inclR (F := F) (Fv F v) z ∈ intLoc F E v := by
  set Z := inclR (F := F) (Fv F v) z
  have key : ∀ y ∈ intLoc F E v, y * Z + sigR _ σ (y * Z) ∈ intLoc F E v := fun y hy => by
    refine intLoc_induction (p := fun y => y * Z + sigR _ σ (y * Z) ∈ intLoc F E v) (fun a ha x => ?_) (by simp)
      (fun _ _ h h' => by convert add_mem h h' using 1; simp only [add_mul, map_add (f := _)]; ring)
      (fun _ h => by convert neg_mem h using 1; simp only [neg_mul, map_neg]; ring) hy
    convert tmul_mem_intLoc (mul_mem ha (trace_mem hB.std (hB.inert v w hw).2.2 (hz.mul x))) 1 using 1
    rw [show a ⊗ₜ[F] (x : E) * Z = a ⊗ₜ[F] (z * x) from (Algebra.TensorProduct.tmul_mul_tmul a 1 _ z).trans (by rw [mul_one, mul_comm])]
    change a ⊗ₜ[F] (z * x) + a ⊗ₜ[F] σ (z * x) = _
    rw [← TensorProduct.tmul_add, add_conj hB.cm, mul_comm a, ← Algebra.smul_def, TensorProduct.smul_tmul,
      Algebra.algebraMap_eq_smul_one]
    rfl
  have hu : w.under (𝓞 F) = v := (under_eq_iff hw w).2 rfl
  obtain ⟨c, hc, -⟩ := existsUnique_isConjAt σ hw hu
  obtain ⟨ϖ, -, -, -, -, ⟨x, hx, hx1⟩, -⟩ := exists_isUnramInv hB.cm hw hc
  obtain ⟨y, rfl⟩ := (toCompl_bijective hw hu).2 x
  have hy := (mem_intLoc_iff hw hu y).2 hx
  have h1 := (mem_intLoc_iff hw hu _).1 (sub_mem (mul_mem (sigR_mem_intLoc σ hy) (key 1 (one_mem _))) (key y hy))
  rw [show sigR _ σ y * (1 * Z + sigR _ σ (1 * Z)) - (y * Z + sigR _ σ (y * Z)) = (sigR _ σ y - y) * Z by
    simp only [one_mul, map_mul]; ring, map_mul, map_sub, ← hc] at h1
  refine (mem_intLoc_iff hw hu _).2 ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_)
  have h2 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h1
  rwa [map_mul, hx1, one_mul] at h2
theorem exists_loc_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {Y : Spc F E n} {r s : ℕ} (hY : Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s)
    (hJ : Y.J.det ≠ 0) (v : Pl F) : ∃ (a g : GL (Fin n) (Fv F v ⊗[F] E)) (l : (Fv F v ⊗[F] E)ˣ),
      (∀ y, (∀ i, y i ∈ intLoc F E v) ↔ a.1 *ᵥ y ∈ latLoc F Y.L v) ∧ a.1 = l.1 • g.1 ∧ Uni σ v Y.J g := by
  have hc := hB.cm
  have hσ := cm_conj_conj hc
  haveI hL : Y.L.IsFullLattice E := hY.elim (·.lat) (·.lat)
  obtain ⟨P, h1, h2⟩ := Frames.exists_rational_frame Y.L v
  let ι := inclR (F := F) (E := E) (Fv F v)
  set G := P.1ᵀ * Y.J * P.1.map σ with hG
  have eG : (bc ι P).1ᵀ * Y.J.map ι * (bc ι P).1.map (sigR _ σ) = G.map ι := by
    rw [hG, Matrix.map_mul, Matrix.map_mul]; rfl
  have one : ∀ G' : Matrix (Fin n) (Fin n) E, G' * G = 1 → G'.map ι * G.map ι = 1 := fun G' h => by
    rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]
  suffices h : ∃ l : (Fv F v ⊗[F] E)ˣ, Int (intLoc F E v) (((l⁻¹).1 * sigR _ σ (l⁻¹).1) • G.map ι) ∧
      ∃ G' : Matrix (Fin n) (Fin n) E, G' * G = 1 ∧ Int (intLoc F E v) ((l.1 * sigR _ σ l.1) • G'.map ι) by
    obtain ⟨l, a1, G', a2, a3⟩ := h
    have e : (l⁻¹ • bc ι P).1ᵀ * Y.J.map ι * (l⁻¹ • bc ι P).1.map (sigR _ σ) = ((l⁻¹).1 * sigR _ σ (l⁻¹).1) • G.map ι := by
      rw [← eG, mul_smul, ← Matrix.mul_smul, ← Matrix.smul_mul, ← Matrix.smul_mul]
      congr 1
      exact Matrix.ext fun i j => map_mul (sigR (Fv F v) σ) (l⁻¹).1 _
    refine ⟨bc ι P, l⁻¹ • bc ι P, l, Frames.frame_of_rational P h1 h2, (smul_inv_smul l _).symm, e ▸ a1, _, a3, ?_⟩
    rw [e, Matrix.smul_mul, Matrix.mul_smul, one G' a2, smul_smul, mul_mul_mul_comm, ← map_mul, Units.mul_inv, map_one, one_mul, one_smul]
  rcases hY with h | h
  · obtain ⟨G', b0, b1, b2⟩ := gram_loc hJ hL.fg (I := IsIntegral ℤ) (fun z hz b => hz.mul b.2) h.dual
      isIntegral_one (fun z hz => ⟨1, (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top, ⟨z, hz⟩, by simp; rfl⟩) P h1 h2
    exact ⟨1, fun i j => by simpa using (b1 i j).mem, G', b0, fun i j => by simpa using (b2 i j).mem⟩
  obtain ⟨δ, d0, d1, d2⟩ := exists_locGen (E := E) v
  obtain ⟨G', b0, b1, b2⟩ := gram_loc hJ hL.fg (I := InD) (fun z hz b => hz.mul b) h.dual d1 d2 P h1 h2
  rw [← hG] at b0 b1
  rcases _root_.GlobalTheory.KFinLoc.split_or_inert_k F E σ B hB v with ⟨⟨τ⟩⟩ | ⟨w, hw⟩
  · have s1 : (G.map σ)ᵀ = -G := (gram_sym (σ : E →+* E) hσ (ε := -1)
      (Matrix.ext fun i j => (h.skew i j).trans (neg_one_mul _).symm) P.1).trans (neg_one_smul _ _)
    have s2 : (G'.map σ)ᵀ = -G' := by
      have e : (G.map σ)ᵀ * (G'.map σ)ᵀ = 1 := by
        rw [← Matrix.transpose_mul]
        change (G'.map (σ : E →+* E) * G.map (σ : E →+* E))ᵀ = 1
        rw [← Matrix.map_mul, b0, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
      rw [← Matrix.one_mul (G'.map σ)ᵀ, ← b0, Matrix.mul_assoc, ← neg_neg G, ← s1, Matrix.neg_mul, e]; simp
    let u := (splitAlgEquiv hc τ).symm
    have fin : ∀ (d : E) (X : Matrix (Fin n) (Fin n) E), (X.map σ)ᵀ = -X → (∀ i j, LocInt v (d * X i j)) →
        Int (intLoc F E v) ((u (τ d, 1) * sigR _ σ (u (τ d, 1))) • X.map ι) := fun d X hX hd i j => by
      have q : ∀ i j, τ d * τ (X i j) ∈ v.adicCompletionIntegers F := fun i j => by
        simpa [inclR] using splitProj_mem τ (hd i j).mem
      have q' : σ (X i j) = -X j i := congrFun (congrFun hX j) i
      refine (mem_intLoc_iff_split hc τ).2 ⟨?_, ?_⟩
      · simpa [u, ι, inclR, ← splitProj_comp] using q i j
      · simpa [u, ι, inclR, splitProj_comp_sigR hc, q'] using q j i
    have e : u (τ δ, 1) * u (τ δ⁻¹, 1) = 1 := by
      rw [← map_mul, Prod.mk_mul_mk, ← map_mul, mul_inv_cancel₀ d0, map_one, mul_one]; exact map_one u
    exact ⟨⟨_, _, e, (mul_comm _ _).trans e⟩, fin _ _ s1 b1, G', b0, fin _ _ s2 b2⟩
  · have i1 := _root_.GlobalTheory.ThK.Dbl.Frame.inD_mem_k hB hw d1
    have i2 := (d2 1 ((inD_iff _).2 (FractionalIdeal.one_le_dual_one ℤ ℚ (FractionalIdeal.one_mem_one _)))).mem
    refine ⟨1, fun i j => ?_, G', b0, fun i j => ?_⟩
    · simpa [← map_mul, d0] using mul_mem i1 (b1 i j).mem
    · simpa [← map_mul, d0] using mul_mem i2 (b2 i j).mem
theorem exists_ad_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {Y : Spc F E n} {r s : ℕ} (hY : Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s)
    (hJ : Y.J.det ≠ 0) (c : InfinitePlace F → GL (Fin n) ℂ) : ∃ a g : GL (Fin n) (AE F E), GlobalTheory.AdelicU.IsLatticeFrame Y.L a ∧
      (∀ v, (∃ l : (Fv F v ⊗[F] E)ˣ, (bc (compFin F E v) a).1 = l.1 • (bc (compFin F E v) g).1) ∧ Uni σ v Y.J (bc (compFin F E v) g)) ∧
      ∀ w, bc (piInf (B.emb w)) g = c w := by
  classical
  haveI hL : Y.L.IsFullLattice E := hY.elim (·.lat) (·.lat)
  obtain ⟨S, hS⟩ := Frames.exists_finset_latLoc_eq (F := F) Y.L
  have h0 : ∀ᶠ v : Pl F in cofinite, v ∉ S ∧ ∀ i j, LocInt v (Y.J i j) ∧ LocInt v (Y.J⁻¹ i j) :=
    S.eventually_cofinite_notMem.and (eventually_all.2 fun i => eventually_all.2 fun j => (ae_locInt _).and (ae_locInt _))
  have key : ∀ v : Pl F, ∃ (a g : GL (Fin n) (Fv F v ⊗[F] E)), (v ∉ Set.Finite.toFinset h0 → a = 1 ∧ g = 1) ∧ ∃ l : (Fv F v ⊗[F] E)ˣ,
      (∀ y, (∀ i, y i ∈ intLoc F E v) ↔ a.1 *ᵥ y ∈ latLoc F Y.L v) ∧ a.1 = l.1 • g.1 ∧ Uni σ v Y.J g := fun v => by
    by_cases hv : v ∈ Set.Finite.toFinset h0
    · obtain ⟨a, g, h⟩ := _root_.GlobalTheory.ThK.Dbl.Frame.exists_loc_k hB hY hJ v
      exact ⟨a, g, fun h => absurd hv h, h⟩
    · have hv' := not_not.1 (mt (Set.Finite.mem_toFinset h0).2 hv)
      refine ⟨1, 1, fun _ => ⟨rfl, rfl⟩, 1, fun y => by simpa using hS v hv'.1 y, (one_smul _ _).symm, ?_⟩
      rw [Uni, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
      refine ⟨fun i j => (hv'.2 i j).1.mem, Y.J⁻¹.map (inclR (F := F) (Fv F v)), fun i j => (hv'.2 i j).2.mem, ?_⟩
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hJ.isUnit, Matrix.map_one _ (map_zero _) (map_one _)]
  choose a g h1 l h2 h3 h4 using key
  let e := fun w => RingEquiv.ofBijective _ (infEmb_bijective hB.cm (B.emb w))
  obtain ⟨a', ha, -⟩ := Frames.exists_GL_of_components _ a (fun v hv => (h1 v hv).1) fun _ => 1
  obtain ⟨g', hg, hg'⟩ := Frames.exists_GL_of_components _ g (fun v hv => (h1 v hv).2) fun w => bc (e w).symm.toRingHom (c w)
  refine ⟨a', g', fun v y => ha v ▸ h2 v y, fun v => ?_, fun w => Units.ext (Matrix.ext fun i j => ?_)⟩
  · rw [ha, hg]; exact ⟨⟨_, h3 v⟩, h4 v⟩
  · exact (congrArg (fun x => e w (x.1 i j)) (hg' w)).trans ((e w).apply_symm_apply _)
end GlobalTheory.ThK.Dbl.Frame
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.HeisOFDblGDeltaTK
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.DblHeis
open Formalism.IndefR.DatumF GlobalTheory.DblTargetDelta GlobalTheory.WeilSchrodinger.DblTargetF
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem heisOF_dblG_deltaT_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (w : Formalism.IndefR.DatumF.WOF F E nS (nT + nT)) (f₁ f₂ : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ w (GlobalTheory.DblTargetDelta.deltaT f₁ f₂) =
          GlobalTheory.DblTargetDelta.deltaT (Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (GlobalTheory.DblTargetDelta.topR w) f₁)
            (Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (-GlobalTheory.DblTargetDelta.botR w) f₂) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT _ _ ξ₀ _ _ w f₁ f₂
  have hn : ∀ x, ‖B.ψ x‖ = 1 := (_root_.GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood_k F E σ B hB).1.2.1
  funext x
  have ht : topR (x + w) = topR x + topR w := rfl
  have hb : -botR (x + w) = -botR x + -botR w := by
    rw [← neg_add]; rfl
  simp only [heisOF, deltaT_apply, ht, hb, symplOHF_dblG, map_mul, conj_psi hn, sub_eq_add_neg, AddChar.map_add_eq_mul]
  ring
end GlobalTheory.DblHeis
end
end
end
