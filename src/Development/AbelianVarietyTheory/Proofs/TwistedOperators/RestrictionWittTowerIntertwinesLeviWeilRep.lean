module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelParsevalThetaInnerProduct
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InclTprodUpdate
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddHaarLeftRightMulAdelicMatricesModule
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfFourierEqZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryEquivInvTransposeOfGramInv

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviElementScalesRestrictionNormSqAbsDet
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedNormSqFourierEqIsotropicMatrixCoeff
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedNormSqFourierEqIsotropicMatrixCoeff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ResNormFourier

theorem resNorm_fourier : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C * V.gram * C' = 1 → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C' * V.gram * C' = 0 → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C' * V.gram * B = 0 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ (μ₀ : Measure (WO V W)) (𝓕₀ : Set (WO V W)), IsCovolOne (ratL W V) μ₀ 𝓕₀ → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), IsCovolOne (ratL W V') μ' 𝓕' → ∀ f, IsThetaFunO ψ V W f → ∀ y : Mx D W.rank r, ∫ w in 𝓕₀, heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y) f w * starRingEnd ℂ (f w) ∂μ₀ = ∫ u, ψ (symplOH V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y) + symplOH V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y)) * GlobalTheory.LeviNorm.resNorm ψ V V' W C C' B μ 𝓨 μ' 𝓕' f u ∂μ := by
  intro D V V' W r C B hs C' h1 h2 h3 ψ hψ μ 𝓨 hY μ₀ 𝓕₀ h0 μ' 𝓕' h' f hf y
  have L := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ V W
  have hR := GlobalTheory.TowerRestrict.res_theta D V V' W r C B hs ψ hψ μ 𝓨 hY
  obtain ⟨-, -, hP⟩ := GlobalTheory.T.mixedModel_parseval_thetaInnerProduct D V V' W r C B hs C' h1 h2 h3 ψ hψ μ 𝓨 hY μ₀ 𝓕₀ h0 μ' 𝓕' h' _ f
    (L.1 _ f hf) hf
  rw [hP]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have hsm : ∀ (c : ℂ) (g : WO V W → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (c • g) =
      c • GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 g := by
    intro c g; funext x
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res, Pi.smul_apply, smul_eq_mul, integral_const_mul]
  have key : ∀ a b : WO V W, heisO ψ V W a (heisO ψ V W b f) =
      ψ (symplOH V W a b + symplOH V W a b) • heisO ψ V W b (heisO ψ V W a f) := by
    intro a b
    rw [L.2.1 a b f, L.2.1 b a f, smul_smul, add_comm b a, GlobalTheory.MixModel.symplOH_skew V W b a,
      ← AddChar.map_add_eq_mul]
    congr 2
    abel
  simp only
  rw [key, hsm, (hR.1 _ (L.1 _ f hf)).2.2.2 y]
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [integral_const_mul]
  rfl

end GlobalTheory.ResNormFourier
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedNormSqFourierEqIsotropicMatrixCoeffStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrictedNormSq_fourier_eq_isotropicMatrixCoeff : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C * V.gram * C' = 1 → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C' * V.gram * C' = 0 → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C' * V.gram * B = 0 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ (μ₀ : Measure (WO V W)) (𝓕₀ : Set (WO V W)), IsCovolOne (ratL W V) μ₀ 𝓕₀ → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), IsCovolOne (ratL W V') μ' 𝓕' → ∀ f, IsThetaFunO ψ V W f → ∀ y : Mx D W.rank r, ∫ w in 𝓕₀, heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y) f w * starRingEnd ℂ (f w) ∂μ₀ = ∫ u, ψ (symplOH V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y) + symplOH V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y)) * GlobalTheory.LeviNorm.resNorm ψ V V' W C C' B μ 𝓨 μ' 𝓕' f u ∂μ := by
  first | exact @GlobalTheory.ResNormFourier.resNorm_fourier | exact GlobalTheory.ResNormFourier.resNorm_fourier | (intros; apply GlobalTheory.ResNormFourier.resNorm_fourier <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOfLeviPhaseCharacterIntegralsEq
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOfLeviPhaseCharacterIntegralsEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LeviNormInj

open GlobalTheory.MixModel

theorem phase_eq (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (W : HSp D) {r : ℕ} (y' : Mx D r W.rank) (u : Mx D W.rank r) :
    GlobalTheory.LeviNorm.phase ψ W (adj (incA D D.host.xi0⁻¹ • (HMul.hMul y' (giA W)))) u =
      ψ (Algebra.trace (AF D.host.F) (AE D) (Matrix.trace (HMul.hMul (y' : Matrix (Fin r) (Fin W.rank) (AE D)) (u : Matrix (Fin W.rank) (Fin r) (AE D))))) := by
  rw [GlobalTheory.LeviNorm.phase_apply, adj_adj]
  congr 2
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, ← mul_assoc, ← map_mul,
    mul_inv_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one, one_mul, Matrix.mul_assoc]
  have h : giA W * gA W = 1 := by
    change (W.gram⁻¹).map (incA D) * W.gram.map (incA D) = 1
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (gram_det_ne W)),
      Matrix.map_one _ (map_zero (incA D)) (map_one (incA D))]
  rw [← Matrix.mul_assoc (giA W), h, Matrix.one_mul]

theorem eq_of_phase_integral_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (W : HSp D) (r : ℕ) (μ : Measure (Mx D W.rank r)), μ.IsAddHaarMeasure → ∀ N₁ N₂ : Mx D W.rank r → ℂ, Continuous N₁ → Continuous N₂ → Integrable N₁ μ → Integrable N₂ μ → (∀ y : Mx D W.rank r, ∫ u, GlobalTheory.LeviNorm.phase ψ W y u * N₁ u ∂μ = ∫ u, GlobalTheory.LeviNorm.phase ψ W y u * N₂ u ∂μ) → N₁ = N₂ := by
  intro D ψ hψ W r μ hμ N₁ N₂ hc₁ hc₂ hi₁ hi₂ h
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.TowerRestrict.lattice_Mx D W.rank r
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  have hcont : ∀ y : Mx D r W.rank, Continuous fun u : Mx D W.rank r =>
      ψ (Algebra.trace (AF D.host.F) (AE D) (Matrix.trace (HMul.hMul (y : Matrix (Fin r) (Fin W.rank) (AE D)) (u : Matrix (Fin W.rank) (Fin r) (AE D))))) :=
    fun y => hψ.1.1.comp (ht.comp (continuous_finsetSum _ fun i _ =>
      ((continuous_const.matrix_mul continuous_id).matrix_elem i i)))
  have hint : ∀ (y : Mx D r W.rank) (N : Mx D W.rank r → ℂ), Integrable N μ → Integrable (fun u =>
      ψ (Algebra.trace (AF D.host.F) (AE D) (Matrix.trace (HMul.hMul (y : Matrix (Fin r) (Fin W.rank) (AE D)) (u : Matrix (Fin W.rank) (Fin r) (AE D))))) * N u) μ := by
    intro y N hN
    have := hN.mul_bdd (hcont y).aestronglyMeasurable (c := 1) (Filter.Eventually.of_forall fun u => (hψ.1.2.1 _).le)
    simpa only [mul_comm] using this
  rw [← sub_eq_zero]
  refine GlobalTheory.AdelicMatFourier.eq_zero_of_fourier_eq_zero D ψ hψ W.rank r μ hμ (N₁ - N₂) (hc₁.sub hc₂) (hi₁.sub hi₂) fun y' => ?_
  have e := h (adj (incA D D.host.xi0⁻¹ • (HMul.hMul y' (giA W))))
  simp only [phase_eq] at e
  simp only [Pi.sub_apply, mul_sub]
  rw [integral_sub (hint y' N₁ hi₁) (hint y' N₂ hi₂), e, sub_self]

end GlobalTheory.LeviNormInj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOfLeviPhaseCharacterIntegralsEqStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_leviPhaseCharacter_integrals_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (W : HSp D) (r : ℕ) (μ : Measure (Mx D W.rank r)), μ.IsAddHaarMeasure → ∀ N₁ N₂ : Mx D W.rank r → ℂ, Continuous N₁ → Continuous N₂ → Integrable N₁ μ → Integrable N₂ μ → (∀ y : Mx D W.rank r, ∫ u, GlobalTheory.LeviNorm.phase ψ W y u * N₁ u ∂μ = ∫ u, GlobalTheory.LeviNorm.phase ψ W y u * N₂ u ∂μ) → N₁ = N₂ := by
  first | exact @GlobalTheory.LeviNormInj.eq_of_phase_integral_eq | exact GlobalTheory.LeviNormInj.eq_of_phase_integral_eq | (intros; apply GlobalTheory.LeviNormInj.eq_of_phase_integral_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplecticHalfIsotropicPartsAddSelfEqTrace
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplecticHalfIsotropicPartsAddSelfEqTrace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IsoPartPairing

open GlobalTheory.MixModel

theorem hO_isoPart {D : D7} (V W : HSp D) {r : ℕ} (C C' : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hC : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C * V.gram * C' = 1) (u y : Mx D W.rank r) :
    hO V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y) =
      (GlobalTheory.MixModel.adj y ⬝ (GlobalTheory.MixModel.gA W ⬝ u)).trace := by
  have hC0 : Cᴴ * V.gram * C' = 1 := hC
  have hC1 : C'ᴴ * V.gram * C = 1 := by
    have h := congrArg Matrix.conjTranspose hC0
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      GlobalTheory.MixModel.gram_conjTranspose, Matrix.conjTranspose_one, ← Matrix.mul_assoc] at h
  have hx : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u = u ⬝ rat (C'ᴴ * V.gram) := rfl
  have hz : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y = y ⬝ rat (Cᴴ * V.gram) := rfl
  have hg : giA V ⬝ adj (rat (Cᴴ * V.gram)) = rat C := by
    rw [← rat_conjTranspose, Matrix.conjTranspose_mul, GlobalTheory.MixModel.gram_conjTranspose,
      Matrix.conjTranspose_conjTranspose, giA, ← rat_mul, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ (GlobalTheory.MixModel.gram_isUnit_det V), Matrix.one_mul]
  rw [hx, hz, hO_eq_trace, adj_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (giA V), hg]
  rw [show rat C ⬝ (adj y ⬝ (gA W ⬝ (u ⬝ rat (C'ᴴ * V.gram)))) = (rat C ⬝ adj y ⬝ gA W ⬝ u) ⬝ rat (C'ᴴ * V.gram) by
    simp only [Matrix.mul_assoc]]
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← rat_mul, hC1, rat_one,
    Matrix.one_mul, Matrix.mul_assoc]

theorem trHalf_add_self {D : D7} (z : AE D) :
    trHalf D z + trHalf D z = Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * z) := by
  show algebraMap D.host.F (AF D.host.F) (1 / 2) * _ + algebraMap D.host.F (AF D.host.F) (1 / 2) * _ = _
  rw [← add_mul, ← map_add (f := _), add_halves, map_one, one_mul]

theorem symplOH_isoPart_add_self : ∀ (D : D7) (V W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C * V.gram * C' = 1 → ∀ u y : Mx D W.rank r, symplOH V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y) + symplOH V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y) = Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * (HMul.hMul (GlobalTheory.MixModel.adj y) (HMul.hMul (GlobalTheory.MixModel.gA W) u)).trace) := by
  intro D V W r C C' hC u y
  rw [symplOH_eq, hO_isoPart V W C C' hC u y, trHalf_add_self]

end GlobalTheory.IsoPartPairing
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplecticHalfIsotropicPartsAddSelfEqTraceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplecticHalf_isotropicParts_add_self_eq_trace : ∀ (D : D7) (V W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C * V.gram * C' = 1 → ∀ u y : Mx D W.rank r, symplOH V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y) + symplOH V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y) = Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * (HMul.hMul (GlobalTheory.MixModel.adj y) (HMul.hMul (GlobalTheory.MixModel.gA W) u)).trace) := by
  first | exact @GlobalTheory.IsoPartPairing.symplOH_isoPart_add_self | exact GlobalTheory.IsoPartPairing.symplOH_isoPart_add_self | (intros; apply GlobalTheory.IsoPartPairing.symplOH_isoPart_add_self <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralLeviPhaseChangeOfVariables
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralLeviPhaseChangeOfVariables
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LeviNorm

variable {D : D7}

def sandwichHomeo {m n : ℕ} (P : GL (Fin m) (AE D)) (Q : GL (Fin n) (AE D)) : Mx D m n ≃ₜ Mx D m n where
  toFun u := HMul.hMul (HMul.hMul P.val u) Q.val
  invFun v := HMul.hMul (HMul.hMul (P⁻¹).val v) (Q⁻¹).val
  left_inv u := by
    simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  right_inv v := by
    simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem phase_sandwich (ψ : AddChar (AF D.host.F) ℂ) (W : HSp D) {r : ℕ} (h : GA D W) (a : GL (Fin r) (AE D))
    (y u : Mx D W.rank r) :
    phase ψ W (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) y) (GlobalTheory.MixModel.adj (a⁻¹).val))
      (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) u) a.val) = phase ψ W y u := by
  rw [phase_apply, phase_apply]
  congr 3
  have hu := GlobalTheory.MixModel.mt_unitary W h⁻¹
  have adj_mul_local {l m n : ℕ} (x : Mx D l m) (y : Mx D m n) :
      GlobalTheory.MixModel.adj (x * y) = GlobalTheory.MixModel.adj y * GlobalTheory.MixModel.adj x := by
    unfold GlobalTheory.MixModel.adj
    rw [Matrix.map_mul, Matrix.transpose_mul]
  change (GlobalTheory.MixModel.adj ((Formalism.L2.Theta.mt W h⁻¹) * y * (GlobalTheory.MixModel.adj (a⁻¹).val)) *
    (GlobalTheory.MixModel.gA W * ((Formalism.L2.Theta.mt W h⁻¹) * u * a.val))).trace = _
  simp only [adj_mul_local, GlobalTheory.MixModel.adj_adj]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (GlobalTheory.MixModel.gA W) (Formalism.L2.Theta.mt W h⁻¹),
    ← Matrix.mul_assoc (GlobalTheory.MixModel.adj (Formalism.L2.Theta.mt W h⁻¹)), hu, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

theorem absE_det_matHom_inv {W : HSp D} (h : GA D W)
    (hh : GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det (Formalism.L2.Theta.matHom W h)) = 1) :
    GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det (Formalism.L2.Theta.matHom W h⁻¹)) = 1 := by
  rw [map_inv, map_inv, map_inv, hh, inv_one]

theorem absE_det_pow_ne {r : ℕ} (a : GL (Fin r) (AE D)) (k : ℕ) :
    ((GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ENNReal) ^ k) ≠ 0 ∧
      ((GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ENNReal) ^ k) ≠ ⊤ :=
  ⟨pow_ne_zero _ (ENNReal.coe_ne_zero.2 ((Group.isUnit (Matrix.GeneralLinearGroup.det a)).map
    (GlobalTheory.Doubling.absE D.host.F D.host.E)).ne_zero), ENNReal.pow_ne_top ENNReal.coe_ne_top⟩


set_option maxHeartbeats 800000 in
theorem integral_phase_sandwich : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (W : HSp D) (r : ℕ) (μ : Measure (Mx D W.rank r)), μ.IsAddHaarMeasure → ∀ (h : GA D W), GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det (matHom W h)) = 1 → ∀ (a : GL (Fin r) (AE D)) (N : Mx D W.rank r → ℂ), Continuous N → Integrable N μ → Integrable (fun u : Mx D W.rank r => N (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) u) a.val)) μ ∧ ∀ y : Mx D W.rank r, ∫ u, GlobalTheory.LeviNorm.phase ψ W (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) y) (GlobalTheory.MixModel.adj (a⁻¹).val)) u * N u ∂μ = ((GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ℝ) : ℂ) ^ W.rank * ∫ u, GlobalTheory.LeviNorm.phase ψ W y u * N (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) u) a.val) ∂μ := by
  intro D ψ _ W r μ hμ h hh a N _ hNi
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  have hmod := GlobalTheory.T.addHaar_leftRightMul_adelicMatrices_module D W.rank r μ hμ (Formalism.L2.Theta.matHom W h⁻¹) a
  have h1 := absE_det_matHom_inv h hh
  rw [h1, ENNReal.coe_one, one_pow, one_mul] at hmod
  obtain ⟨hc0, hcT⟩ := absE_det_pow_ne a W.rank
  let e := (sandwichHomeo (Formalism.L2.Theta.matHom W h⁻¹) a).toMeasurableEquiv
  have he : ∀ u, e u = HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) u) a.val := fun _ => rfl
  have hmap : (Measure.map (fun u : Mx D W.rank r =>
      (HMul.hMul (HMul.hMul (Formalism.L2.Theta.matHom W h⁻¹).val (u : Matrix (Fin W.rank) (Fin r) (AE D))) a.val :
        Mx D W.rank r)) μ) = Measure.map e μ := rfl
  rw [hmap] at hmod
  refine ⟨?_, fun y => ?_⟩
  · rw [hmod, integrable_smul_measure hc0 hcT, integrable_map_equiv] at hNi
    exact hNi
  · conv_lhs => rw [hmod]
    rw [integral_smul_measure, integral_map_equiv]
    simp only [he, phase_sandwich]
    rw [ENNReal.toReal_pow, ENNReal.coe_toReal, Complex.real_smul]
    push_cast
    rfl

end GlobalTheory.LeviNorm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralLeviPhaseChangeOfVariablesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_levi_phase_change_of_variables : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (W : HSp D) (r : ℕ) (μ : Measure (Mx D W.rank r)), μ.IsAddHaarMeasure → ∀ (h : GA D W), GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det (matHom W h)) = 1 → ∀ (a : GL (Fin r) (AE D)) (N : Mx D W.rank r → ℂ), Continuous N → Integrable N μ → Integrable (fun u : Mx D W.rank r => N (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) u) a.val)) μ ∧ ∀ y : Mx D W.rank r, ∫ u, GlobalTheory.LeviNorm.phase ψ W (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) y) (GlobalTheory.MixModel.adj (a⁻¹).val)) u * N u ∂μ = ((GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ℝ) : ℂ) ^ W.rank * ∫ u, GlobalTheory.LeviNorm.phase ψ W y u * N (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) u) a.val) ∂μ := by
  first | exact @GlobalTheory.LeviNorm.integral_phase_sandwich | exact GlobalTheory.LeviNorm.integral_phase_sandwich | (intros; apply GlobalTheory.LeviNorm.integral_phase_sandwich <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumTransportsHeisenbergMatrixCoeffs
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumTransportsHeisenbergMatrixCoeffs
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilCoeff

theorem heis_coeff_eq : ∀ (D : D7) (V W : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (g : GA D V) (h : GA D W) (f : WO V W → ℂ), IsThetaFunO ψ V W f → ∀ (μ₀ : Measure (WO V W)) (𝓕₀ : Set (WO V W)), μ₀.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕₀ μ₀ → ∀ w₀ : WO V W, ∫ w in 𝓕₀, heisO ψ V W (actO V W g h w₀) (ω (g, h) f) w * starRingEnd ℂ (ω (g, h) f w) ∂μ₀ = ∫ w in 𝓕₀, heisO ψ V W w₀ f w * starRingEnd ℂ (f w) ∂μ₀ := by
  intro D V W ψ χS χT ω hω g h f hf μ₀ 𝓕₀ hμ h𝓕 w₀
  have hf1 := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hω.std V W).1 w₀ f hf
  rw [← hω.om_heis g h w₀ f hf]
  exact GlobalTheory.Mem.LiftPolar.scalar_eq D ψ hω.std V W μ₀ 𝓕₀ hμ h𝓕 (ω (g, h))
    (fun f hf => hω.om_pres (g, h) f hf) (fun f hf => hω.om_unit μ₀ 𝓕₀ hμ h𝓕 (g, h) f hf) _ f hf1 hf

end GlobalTheory.WeilCoeff
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumTransportsHeisenbergMatrixCoeffsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDatum_transports_heisenbergMatrixCoeffs : ∀ (D : D7) (V W : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (g : GA D V) (h : GA D W) (f : WO V W → ℂ), IsThetaFunO ψ V W f → ∀ (μ₀ : Measure (WO V W)) (𝓕₀ : Set (WO V W)), μ₀.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕₀ μ₀ → ∀ w₀ : WO V W, ∫ w in 𝓕₀, heisO ψ V W (actO V W g h w₀) (ω (g, h) f) w * starRingEnd ℂ (ω (g, h) f w) ∂μ₀ = ∫ w in 𝓕₀, heisO ψ V W w₀ f w * starRingEnd ℂ (f w) ∂μ₀ := by
  first | exact @GlobalTheory.WeilCoeff.heis_coeff_eq | exact GlobalTheory.WeilCoeff.heis_coeff_eq | (intros; apply GlobalTheory.WeilCoeff.heis_coeff_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsConstSqNormTwoHaarFundamentalDomains
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsConstSqNormTwoHaarFundamentalDomains
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Twist.NormRed

theorem sq_norm_two_haar : ∀ (D : D7) (V' W : HSp D) (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∀ (μ'' : Measure (WO V' W)) (𝓕'' : Set (WO V' W)), IsCovolOne (ratL W V') μ'' 𝓕'' → ∃ c : ENNReal, ∀ g : WO V' W → ℂ, Continuous g → (∀ γ ∈ ratL W V', ∀ w, ‖g (γ + w)‖ = ‖g w‖) → ∫⁻ x in 𝓕', ‖g x‖ₑ ^ 2 ∂μ' = c * ∫⁻ x in 𝓕'', ‖g x‖ₑ ^ 2 ∂μ'' := by
  intro D V' W μ' 𝓕' hμ' hF' μ'' 𝓕'' h''
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank V'.rank
  haveI : BorelSpace (WO V' W) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (WO V' W) := i1
  haveI : LocallyCompactSpace (WO V' W) := i2
  haveI : SecondCountableTopology (WO V' W) := i3
  haveI : T2Space (WO V' W) := i4
  haveI : DiscreteTopology (ratL W V') := i5
  haveI : TopologicalSpace.SeparableSpace (ratL W V') := inferInstance
  haveI : Countable (ratL W V') := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : MeasurableConstVAdd (ratL W V') (WO V' W) :=
    ⟨fun c => (continuous_const.add continuous_id).measurable⟩
  obtain ⟨hμ'', hF'', -⟩ := h''
  haveI : VAddInvariantMeasure (ratL W V') (WO V' W) μ'' :=
    ⟨fun c s _ => measure_preimage_add μ'' (c : WO V' W) s⟩
  have e := Measure.isAddLeftInvariant_eq_smul μ' μ''
  set c := Measure.addHaarScalarFactor μ' μ''
  have hc : c ≠ 0 := (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ' μ'').ne'
  have hac : μ'' ≪ μ' := by
    rw [e]; exact Measure.absolutelyContinuous_smul (by exact_mod_cast hc)
  have hF2 : IsAddFundamentalDomain (ratL W V') 𝓕' μ'' := hF'.mono hac
  refine ⟨(c : ENNReal), fun g hg hper => ?_⟩
  have hp : ∀ (γ : ratL W V') (x : WO V' W), ‖g (γ +ᵥ x)‖ₑ ^ 2 = ‖g x‖ₑ ^ 2 := by
    intro γ x
    rw [AddSubgroup.vadd_def, vadd_eq_add]
    have h1 : ‖g ((γ : WO V' W) + x)‖₊ = ‖g x‖₊ := NNReal.eq (hper γ γ.2 x)
    simp only [enorm_eq_nnnorm, h1]
  rw [e, Measure.restrict_smul, lintegral_smul_measure, hF2.setLIntegral_eq hF'' _ hp]
  rfl

end GlobalTheory.Twist.NormRed
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsConstSqNormTwoHaarFundamentalDomainsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_const_sqNorm_two_haar_fundamentalDomains : ∀ (D : D7) (V' W : HSp D) (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∀ (μ'' : Measure (WO V' W)) (𝓕'' : Set (WO V' W)), IsCovolOne (ratL W V') μ'' 𝓕'' → ∃ c : ENNReal, ∀ g : WO V' W → ℂ, Continuous g → (∀ γ ∈ ratL W V', ∀ w, ‖g (γ + w)‖ = ‖g w‖) → ∫⁻ x in 𝓕', ‖g x‖ₑ ^ 2 ∂μ' = c * ∫⁻ x in 𝓕'', ‖g x‖ₑ ^ 2 ∂μ'' := by
  first | exact @GlobalTheory.Twist.NormRed.sq_norm_two_haar | exact GlobalTheory.Twist.NormRed.sq_norm_two_haar | (intros; apply GlobalTheory.Twist.NormRed.sq_norm_two_haar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionIsotropicPartHomOfFrameMul
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionIsotropicPartHomOfFrameMul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IsoFrameAct

open scoped GlobalTheory.MixModel

theorem actO_isoPart_of_mul : ∀ (D : D7) (V W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (a : GL (Fin r) (AE D)) (m : GA D V), HMul.hMul (Formalism.L2.Theta.mt V m) (C.map (incA D)) = HMul.hMul (C.map (incA D)) a.val → ∀ (h : GA D W) (z : Mx D W.rank r), actO V W m h (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C z) = GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h) z) (GlobalTheory.MixModel.adj a.val)) := by
  intro D V W r C a m hm h z
  have e : (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C * V.gram).map (incA D) =
      GlobalTheory.MixModel.adj (C.map (incA D)) * GlobalTheory.MixModel.gA V := by
    change GlobalTheory.MixModel.rat (Cᴴ * V.gram) = _
    exact Matrix.map_mul
  have hg : GlobalTheory.MixModel.gA V * GlobalTheory.MixModel.giA V = 1 := by
    change (V.gram.map (incA D)) * (V.gram⁻¹.map (incA D)) = 1
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (gram_det_ne V))]
    exact Matrix.map_one _ (map_zero (incA D)) (map_one (incA D))
  have hg' : GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.gA V = 1 := by
    change (V.gram⁻¹.map (incA D)) * (V.gram.map (incA D)) = 1
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (gram_det_ne V))]
    exact Matrix.map_one _ (map_zero (incA D)) (map_one (incA D))
  have adjmul {l n k : ℕ} (x : Mx D l n) (y : Mx D n k) :
      GlobalTheory.MixModel.adj (x * y) = GlobalTheory.MixModel.adj y * GlobalTheory.MixModel.adj x :=
    Formalism.UG.cT_mul (cA D) x y
  have hinv : Formalism.L2.Theta.mt V m⁻¹ = GlobalTheory.MixModel.giA V *
      (GlobalTheory.MixModel.adj (Formalism.L2.Theta.mt V m) * GlobalTheory.MixModel.gA V) := by
    have hh : GlobalTheory.MixModel.giA V * (GlobalTheory.MixModel.adj (Formalism.L2.Theta.mt V m) * GlobalTheory.MixModel.gA V) * Formalism.L2.Theta.mt V m = 1 := by
      have hr : GlobalTheory.MixModel.adj (Formalism.L2.Theta.mt V m) * GlobalTheory.MixModel.gA V * Formalism.L2.Theta.mt V m = GlobalTheory.MixModel.gA V := mt_rel V m
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (GlobalTheory.MixModel.adj _), hr, hg']
    rw [← Matrix.one_mul (Formalism.L2.Theta.mt V m⁻¹), ← hh, Matrix.mul_assoc]
    have hm_inv : Formalism.L2.Theta.mt V m * Formalism.L2.Theta.mt V m⁻¹ = 1 := by
      change (m.val * m⁻¹.val).val = 1
      exact congrArg Units.val (mul_inv_cancel m.val)
    rw [hm_inv, Matrix.mul_one]
  have key : GlobalTheory.MixModel.adj (C.map (incA D)) * (GlobalTheory.MixModel.gA V * (GlobalTheory.MixModel.giA V *
      (GlobalTheory.MixModel.adj (Formalism.L2.Theta.mt V m) * GlobalTheory.MixModel.gA V))) =
      GlobalTheory.MixModel.adj a.val * (GlobalTheory.MixModel.adj (C.map (incA D)) * GlobalTheory.MixModel.gA V) := by
    rw [← Matrix.mul_assoc (GlobalTheory.MixModel.gA V), hg, Matrix.one_mul, ← Matrix.mul_assoc, ← adjmul, hm, adjmul,
      Matrix.mul_assoc]
  change Formalism.L2.Theta.mt W h * (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C z) * Formalism.L2.Theta.mt V m⁻¹ = _
  rw [hinv]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart]
  rw [e]
  simp only [Matrix.mul_assoc]
  rw [key]

end GlobalTheory.IsoFrameAct

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionIsotropicPartHomOfFrameMulStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilAction_isotropicPartHom_of_frameMul : ∀ (D : D7) (V W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (a : GL (Fin r) (AE D)) (m : GA D V), HMul.hMul (Formalism.L2.Theta.mt V m) (C.map (incA D)) = HMul.hMul (C.map (incA D)) a.val → ∀ (h : GA D W) (z : Mx D W.rank r), actO V W m h (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C z) = GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h) z) (GlobalTheory.MixModel.adj a.val)) := by
  first | exact @GlobalTheory.IsoFrameAct.actO_isoPart_of_mul | exact GlobalTheory.IsoFrameAct.actO_isoPart_of_mul | (intros; apply GlobalTheory.IsoFrameAct.actO_isoPart_of_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviElementScalesRestrictionNormSqAbsDet
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LeviNorm

variable {D : D7}

theorem heisO_isoPart_zero (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) {r : ℕ}
    (C' : Matrix (Fin V.rank) (Fin r) D.host.E) (F : WO V W → ℂ) :
    heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' 0) F = F := by
  have h0 : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' 0 = 0 := Matrix.zero_mul _
  funext w
  rw [h0]
  simp only [heisO, GlobalTheory.MixModel.symplOH_zero_right, AddChar.map_zero_eq_one, one_mul, add_zero]


set_option maxHeartbeats 1000000 in
theorem norm_levi : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∀ (a : GL (Fin r) (AE D)) (g' : GA D V') (m : GA D V), HMul.hMul (Formalism.L2.Theta.mt V m) (C.map (incA D)) = HMul.hMul (C.map (incA D)) a.val → HMul.hMul (Formalism.L2.Theta.mt V m) (B.map (incA D)) = HMul.hMul (B.map (incA D)) (Formalism.L2.Theta.mt V' g') → ∀ (h : GA D W) (f : WO V W → ℂ), IsThetaFunO ψ V W f → ∫⁻ x in 𝓕', ‖GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (m, h) f) x‖ₑ ^ 2 ∂μ' = (GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ENNReal) ^ W.rank * ∫⁻ x in 𝓕', ‖GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f x‖ₑ ^ 2 ∂μ' := by
  intro D V V' W r C B hs ψ χS χT ω hω μ 𝓨 hμ μ' 𝓕' hμ' h𝓕' a g' m hC _hB h f hf
  have hstd : IsStdChar D ψ (-1) := hω.std
  obtain ⟨C', h1, h2, h3⟩ := GlobalTheory.TwistDual.exists_isotropic_dual D V V' r C B hs
  obtain ⟨μ₀, 𝓕₀, h0⟩ := GlobalTheory.MixModel.exists_isCovolOne D W.rank V.rank
  obtain ⟨μ'', 𝓕'', h''⟩ := GlobalTheory.MixModel.exists_isCovolOne D W.rank V'.rank
  have hres := GlobalTheory.TowerRestrict.res_theta D V V' W r C B hs ψ hstd μ 𝓨 hμ
  have hΩf : IsThetaFunO ψ V W (ω (m, h) f) := hω.om_pres _ f hf
  have pΩ := GlobalTheory.T.mixedModel_parseval_thetaInnerProduct D V V' W r C B hs C' h1 h2 h3 ψ hstd μ 𝓨 hμ μ₀ 𝓕₀ h0 μ'' 𝓕'' h'' _ _ hΩf hΩf
  have pf := GlobalTheory.T.mixedModel_parseval_thetaInnerProduct D V V' W r C B hs C' h1 h2 h3 ψ hstd μ 𝓨 hμ μ₀ 𝓕₀ h0 μ'' 𝓕'' h'' f f hf hf
  obtain ⟨N₁, hN₁⟩ : ∃ N : Mx D W.rank r → ℂ, N = resNorm ψ V V' W C C' B μ 𝓨 μ'' 𝓕'' (ω (m, h) f) := ⟨_, rfl⟩
  obtain ⟨N₀, hN₀⟩ : ∃ N : Mx D W.rank r → ℂ, N = resNorm ψ V V' W C C' B μ 𝓨 μ'' 𝓕'' f := ⟨_, rfl⟩
  have hN₁c : Continuous N₁ := by rw [hN₁]; exact pΩ.1
  have hN₁i : Integrable N₁ μ := by rw [hN₁]; exact pΩ.2.1
  have hN₀c : Continuous N₀ := by rw [hN₀]; exact pf.1
  have hN₀i : Integrable N₀ μ := by rw [hN₀]; exact pf.2.1
  obtain ⟨k, hk⟩ : ∃ k : ℂ, k = ((GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ℝ) : ℂ) ^ W.rank :=
    ⟨_, rfl⟩
  have hcov := GlobalTheory.T.integral_levi_phase_change_of_variables D ψ hstd W r μ hμ.1 h (GlobalTheory.T.tensorIdeleAbs_det_unitaryAdelic_eq_one D W h) a N₀ hN₀c hN₀i
  have hph : ∀ y u : Mx D W.rank r, ψ (symplOH V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y) +
      symplOH V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y)) = phase ψ W y u :=
    fun y u => by rw [phase_apply, GlobalTheory.T.symplecticHalf_isotropicParts_add_self_eq_trace D V W r C C' h1 u y]
  rw [← hk] at hcov
  have hφ : Continuous fun u : Mx D W.rank r => (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) u) a.val : Mx D W.rank r) :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  obtain ⟨N₂, hN₂⟩ : ∃ N₂ : Mx D W.rank r → ℂ,
      N₂ = fun u : Mx D W.rank r => k * N₀ (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) u) a.val) := ⟨_, rfl⟩
  have hN₂c : Continuous N₂ := by rw [hN₂]; exact continuous_const.mul (hN₀c.comp hφ)
  have hN₂i : Integrable N₂ μ := by rw [hN₂]; exact hcov.1.const_mul k
  have key : N₁ = N₂ := GlobalTheory.T.eq_of_leviPhaseCharacter_integrals_eq D ψ hstd W r μ hμ.1 N₁ N₂ hN₁c hN₂c hN₁i hN₂i (fun y => by
    have s1 := GlobalTheory.T.restrictedNormSq_fourier_eq_isotropicMatrixCoeff D V V' W r C B hs C' h1 h2 h3 ψ hstd μ 𝓨 hμ μ₀ 𝓕₀ h0 μ'' 𝓕'' h'' _ hΩf y
    have hz : HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h) (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) y)
        (GlobalTheory.MixModel.adj (a⁻¹).val))) (GlobalTheory.MixModel.adj a.val) = y := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, GlobalTheory.MixModel.mt_mul_inv, Matrix.one_mul, Matrix.mul_assoc,
        ← GlobalTheory.MixModel.adj_mul, Units.mul_inv, GlobalTheory.MixModel.adj_one, Matrix.mul_one]
    have s2 := GlobalTheory.T.weilDatum_transports_heisenbergMatrixCoeffs D V W ψ χS χT ω hω m h f hf μ₀ 𝓕₀ h0.1 h0.2.1 (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C
      (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) y) (GlobalTheory.MixModel.adj (a⁻¹).val)))
    rw [GlobalTheory.T.weilAction_isotropicPartHom_of_frameMul D V W r C a m hC h, hz] at s2
    have s3 := GlobalTheory.T.restrictedNormSq_fourier_eq_isotropicMatrixCoeff D V V' W r C B hs C' h1 h2 h3 ψ hstd μ 𝓨 hμ μ₀ 𝓕₀ h0 μ'' 𝓕'' h'' f hf
      (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) y) (GlobalTheory.MixModel.adj (a⁻¹).val))
    simp only [hph] at s1 s3
    rw [← hN₁] at s1
    rw [← hN₀] at s3
    rw [← s1, s2, s3, hcov.2 y, hN₂, ← integral_const_mul]
    congr 1
    funext u
    ring)
  have e0 := congrFun key 0
  rw [hN₁, hN₂, hN₀] at e0
  simp only [resNorm, Matrix.mul_zero, Matrix.zero_mul, heisO_isoPart_zero] at e0
  obtain ⟨p1, fin1, eq1⟩ := GlobalTheory.T.thetaFunction_periodicNorm_finite_sqIntegral D ψ hstd V' W μ'' 𝓕'' h'' _ (hres.1 _ hΩf).2.1
  obtain ⟨p2, fin2, eq2⟩ := GlobalTheory.T.thetaFunction_periodicNorm_finite_sqIntegral D ψ hstd V' W μ'' 𝓕'' h'' _ (hres.1 f hf).2.1
  rw [eq1, eq2, hk] at e0
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_const_sqNorm_two_haar_fundamentalDomains D V' W μ' 𝓕' hμ' h𝓕' μ'' 𝓕'' h''
  rw [hc _ (hres.1 _ hΩf).2.1.cont p1, hc _ (hres.1 f hf).2.1.cont p2]
  have eR : (∫⁻ x in 𝓕'', ‖GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (m, h) f) x‖ₑ ^ 2 ∂μ'').toReal =
      ((GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ℝ)) ^ W.rank *
        (∫⁻ x in 𝓕'', ‖GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f x‖ₑ ^ 2 ∂μ'').toReal := by
    exact_mod_cast e0
  have eE : ∫⁻ x in 𝓕'', ‖GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (m, h) f) x‖ₑ ^ 2 ∂μ'' =
      (GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ENNReal) ^ W.rank *
        ∫⁻ x in 𝓕'', ‖GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f x‖ₑ ^ 2 ∂μ'' := by
    rw [← ENNReal.toReal_eq_toReal_iff' fin1 (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) fin2),
      ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal]
    exact eR
  rw [eE, mul_left_comm]

end GlobalTheory.LeviNorm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviElementScalesRestrictionNormSqAbsDetStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leviElement_scales_restrictionNormSq_absDet : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∀ (a : GL (Fin r) (AE D)) (g' : GA D V') (m : GA D V), HMul.hMul (Formalism.L2.Theta.mt V m) (C.map (incA D)) = HMul.hMul (C.map (incA D)) a.val → HMul.hMul (Formalism.L2.Theta.mt V m) (B.map (incA D)) = HMul.hMul (B.map (incA D)) (Formalism.L2.Theta.mt V' g') → ∀ (h : GA D W) (f : WO V W → ℂ), IsThetaFunO ψ V W f → ∫⁻ x in 𝓕', ‖GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (m, h) f) x‖ₑ ^ 2 ∂μ' = (GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ENNReal) ^ W.rank * ∫⁻ x in 𝓕', ‖GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f x‖ₑ ^ 2 ∂μ' := by
  first | exact @GlobalTheory.LeviNorm.norm_levi | exact GlobalTheory.LeviNorm.norm_levi | (intros; apply GlobalTheory.LeviNorm.norm_levi <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictionWittTowerIntertwinesLeviWeilRep
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped GlobalTheory.MixModel

namespace GlobalTheory.LeviScalar

variable {D : D7}

open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

theorem proj_mul_mt_inv (V V' : HSp D) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (g' : GA D V') (m : GA D V)
    (hB : HMul.hMul (mt V m) (B.map (incA D)) = HMul.hMul (B.map (incA D)) (mt V' g')) :
    HMul.hMul ((V'.gram⁻¹ * adj D B * V.gram).map (incA D)) (mt V m⁻¹) =
      HMul.hMul (mt V' g'⁻¹) ((V'.gram⁻¹ * adj D B * V.gram).map (incA D)) := by
  have hadj : adj D B = Bᴴ := GlobalTheory.MixModel.cT_sig B
  have hP : (V'.gram⁻¹ * adj D B * V.gram).map (incA D) =
      GlobalTheory.MixModel.giA V' * GlobalTheory.MixModel.adj (GlobalTheory.MixModel.rat B) * GlobalTheory.MixModel.gA V := by
    rw [hadj]
    change GlobalTheory.MixModel.rat (V'.gram⁻¹ * Bᴴ * V.gram) = _
    rw [GlobalTheory.MixModel.rat_mul, GlobalTheory.MixModel.rat_mul, GlobalTheory.MixModel.rat_conjTranspose]
    rfl
  have hB' : mt V m * GlobalTheory.MixModel.rat B = GlobalTheory.MixModel.rat B * mt V' g' := hB
  have key : GlobalTheory.MixModel.adj (GlobalTheory.MixModel.rat B) * GlobalTheory.MixModel.adj (mt V m) =
      GlobalTheory.MixModel.adj (mt V' g') * GlobalTheory.MixModel.adj (GlobalTheory.MixModel.rat B) := by
    rw [← GlobalTheory.MixModel.adj_mul, ← GlobalTheory.MixModel.adj_mul, hB']
  rw [hP, GlobalTheory.MixModel.mt_inv, GlobalTheory.MixModel.mt_inv]
  simp only [Matrix.mul_assoc, GlobalTheory.MixModel.gA_giA_cancel]
  rw [← Matrix.mul_assoc (GlobalTheory.MixModel.adj (GlobalTheory.MixModel.rat B)), key, Matrix.mul_assoc]

theorem actO_midPart (V V' W : HSp D) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (g' : GA D V') (m : GA D V)
    (hB : HMul.hMul (mt V m) (B.map (incA D)) = HMul.hMul (B.map (incA D)) (mt V' g')) (h : GA D W) (x : WO V' W) :
    actO V W m h (midPart V V' W B x) = midPart V V' W B (actO V' W g' h x) := by
  have hq := proj_mul_mt_inv V V' B g' m hB
  unfold midPart
  rw [GlobalTheory.MixModel.actO_eq, GlobalTheory.MixModel.actO_eq]
  generalize (V'.gram⁻¹ * adj D B * V.gram).map (incA D) = P at hq ⊢
  simp only [Matrix.mul_assoc]
  rw [hq]

theorem actO_inv_actO (S T : HSp D) (g : GA D S) (h : GA D T) (x : WO S T) :
    actO S T g⁻¹ h⁻¹ (actO S T g h x) = x := by
  rw [GlobalTheory.MixModel.actO_eq, GlobalTheory.MixModel.actO_eq, inv_inv]
  simp only [Matrix.mul_assoc, GlobalTheory.MixModel.mt_inv_mul, Matrix.mul_one]
  rw [← Matrix.mul_assoc, GlobalTheory.MixModel.mt_inv_mul, Matrix.one_mul]

theorem heisO_smul (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T w (c • f) = c • heisO ψ S T w f := by
  ext x
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem absE_ne_zero (u : (AE D)ˣ) : GlobalTheory.Doubling.absE D.host.F D.host.E u ≠ 0 := ((Group.isUnit u).map (GlobalTheory.Doubling.absE D.host.F D.host.E)).ne_zero

theorem detPow_pos {t : ℕ} (a : GL (Fin t) (AE D)) (n : ℕ) : 0 < GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a n := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow
  exact Real.rpow_pos_of_pos (NNReal.coe_pos.2 (pos_iff_ne_zero.2 (absE_ne_zero _))) _

theorem enorm_inv_detPow_sq {t : ℕ} (a : GL (Fin t) (AE D)) (n : ℕ) :
    ‖((GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a n : ℂ))⁻¹‖ₑ ^ 2 *
      (GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ENNReal) ^ n = 1 := by
  have ht : (0 : ℝ) < (GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ℝ) :=
    NNReal.coe_pos.2 (pos_iff_ne_zero.2 (absE_ne_zero _))
  have hd : 0 < GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a n := detPow_pos a n
  have hsq : (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a n) ^ 2 =
      (GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ℝ) ^ n := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul ht.le, ← Real.rpow_natCast _ n]
    congr 1
    push_cast
    ring
  have hn : ‖((GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a n : ℂ))⁻¹‖ₑ = ENNReal.ofReal (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a n)⁻¹ := by
    rw [← ofReal_norm_eq_enorm, norm_inv, Complex.norm_real, Real.norm_of_nonneg hd.le]
  rw [hn, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_pow (inv_nonneg.2 hd.le),
    ← ENNReal.ofReal_pow ht.le, ← ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.2 hd.le) _), ← hsq, inv_pow,
    inv_mul_cancel₀ (pow_ne_zero _ hd.ne'), ENNReal.ofReal_one]

def thetaSpace (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : Submodule ℂ (WO S T → ℂ) where
  carrier := {f | IsThetaFunO ψ S T f}
  zero_mem' := GlobalTheory.OrientedHeis.theta_zero
  add_mem' := fun hf hg => GlobalTheory.OrientedHeis.theta_add hf hg
  smul_mem' := fun c _ hf => GlobalTheory.OrientedHeis.theta_smul c hf

theorem eq_zero_of_lintegral {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (hcv : IsCovolOne (ratL T S) μ 𝓕) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (h0 : ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ = 0) : f = 0 := by
  apply GlobalTheory.ThetaSchurBdd.thetaFunction_eq_zero_of_meanSquare_zero hψ hcv hf
  unfold nrm2
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun w => by positivity)
    (GlobalTheory.ThetaSchurBdd.integrable_sq hψ hcv.2.2 hf).aestronglyMeasurable]
  have h2 : ∫⁻ w in 𝓕, ENNReal.ofReal (‖f w‖ ^ 2) ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ := by
    congr 1
    funext w
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  rw [h2, h0, ENNReal.toReal_zero]

theorem main : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (χS' χT' : (AE D)ˣ →* Circle) (ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)), IsWeilDatumO ψ V' W χS' χT' ω' → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ (a : GL (Fin r) (AE D)) (g' : GA D V') (m : GA D V), HMul.hMul (Formalism.L2.Theta.mt V m) (C.map (incA D)) = HMul.hMul (C.map (incA D)) a.val → HMul.hMul (Formalism.L2.Theta.mt V m) (B.map (incA D)) = HMul.hMul (B.map (incA D)) (Formalism.L2.Theta.mt V' g') → ∀ h : GA D W, ∃ c : Circle, ∀ f, IsThetaFunO ψ V W f → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (m, h) f) = ((c : ℂ) * (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a W.rank : ℂ)) • ω' (g', h) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f) := by
  intro D V V' W r C B hs ψ χS χT ω hω χS' χT' ω' hω' μ 𝓨 hcv a g' m hC hB h
  have hψ : IsStdChar D ψ (-1) := hω.std
  have hres := GlobalTheory.TowerRestrict.res_theta D V V' W r C B hs ψ hψ μ 𝓨 hcv
  have hheis := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ V W).1
  obtain ⟨μ', 𝓕', hcv'⟩ := GlobalTheory.MixModel.exists_isCovolOne D W.rank V'.rank
  rw [← GlobalTheory.MixModel.ratL_eq] at hcv'

  let Θ := thetaSpace ψ V W
  let R : Θ →ₗ[ℂ] (WO V' W → ℂ) :=
    { toFun := fun f => res V V' W C B μ 𝓨 f
      map_add' := fun f g => by
        funext x
        show ∫ y in 𝓨, ((f : WO V W → ℂ) + g) (isoPart V W C y + midPart V V' W B x) ∂μ =
          (∫ y in 𝓨, (f : WO V W → ℂ) (isoPart V W C y + midPart V V' W B x) ∂μ) +
            ∫ y in 𝓨, (g : WO V W → ℂ) (isoPart V W C y + midPart V V' W B x) ∂μ
        simp only [Pi.add_apply]
        exact integral_add ((hres.1 f f.2).1 x) ((hres.1 g g.2).1 x)
      map_smul' := fun c f => by
        funext x
        show ∫ y in 𝓨, (c • (f : WO V W → ℂ)) (isoPart V W C y + midPart V V' W B x) ∂μ =
          c * ∫ y in 𝓨, (f : WO V W → ℂ) (isoPart V W C y + midPart V V' W B x) ∂μ
        simp only [Pi.smul_apply, smul_eq_mul]
        exact integral_const_mul c _ }
  let Φ : Θ →ₗ[ℂ] (WO V' W → ℂ) :=
    R ∘ₗ (ω (m, h)).restrict (p := Θ) (q := Θ) (fun f hf => hω.om_pres (m, h) f hf)

  have hker : LinearMap.ker R ≤ LinearMap.ker Φ := by
    intro f hf
    rw [LinearMap.mem_ker] at hf ⊢
    have hf0 : res V V' W C B μ 𝓨 f = 0 := hf
    have hθ : IsThetaFunO ψ V' W (res V V' W C B μ 𝓨 (ω (m, h) f)) :=
      (hres.1 _ (hω.om_pres (m, h) f f.2)).2.1
    have hsq := GlobalTheory.T.leviElement_scales_restrictionNormSq_absDet D V V' W r C B hs ψ χS χT ω hω μ 𝓨 hcv μ' 𝓕' hcv'.1 hcv'.2.1 a g' m hC hB h f f.2
    rw [hf0] at hsq
    simp only [Pi.zero_apply, enorm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      MeasureTheory.lintegral_const, zero_mul, mul_zero] at hsq
    exact eq_zero_of_lintegral hψ hcv' hθ hsq

  let N₀ : LinearMap.range R →ₗ[ℂ] (WO V' W → ℂ) :=
    (LinearMap.ker R).liftQ Φ hker ∘ₗ R.quotKerEquivRange.symm.toLinearMap
  obtain ⟨Nf, hN⟩ := LinearMap.exists_extend N₀
  have hNf : ∀ f, IsThetaFunO ψ V W f → Nf (res V V' W C B μ 𝓨 f) = res V V' W C B μ 𝓨 (ω (m, h) f) := by
    intro f hf
    let F : Θ := ⟨f, hf⟩
    have e1 : Nf (R F) = N₀ ⟨R F, LinearMap.mem_range_self R F⟩ := by
      rw [← hN]
      rfl
    show Nf (R F) = Φ F
    rw [e1]
    show (LinearMap.ker R).liftQ Φ hker (R.quotKerEquivRange.symm ⟨R F, LinearMap.mem_range_self R F⟩) = Φ F
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl

  let d : ℂ := (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a W.rank : ℂ)
  have hd0 : d ≠ 0 := Complex.ofReal_ne_zero.2 (detPow_pos a W.rank).ne'
  let M : Module.End ℂ (WO V' W → ℂ) := d⁻¹ • (ω' (g'⁻¹, h⁻¹) * Nf)
  have hMres : ∀ f, IsThetaFunO ψ V W f →
      M (res V V' W C B μ 𝓨 f) = d⁻¹ • ω' (g'⁻¹, h⁻¹) (res V V' W C B μ 𝓨 (ω (m, h) f)) := by
    intro f hf
    show d⁻¹ • ω' (g'⁻¹, h⁻¹) (Nf (res V V' W C B μ 𝓨 f)) = _
    rw [hNf f hf]
  have hθω : ∀ f, IsThetaFunO ψ V W f → IsThetaFunO ψ V' W (res V V' W C B μ 𝓨 (ω (m, h) f)) :=
    fun f hf => (hres.1 _ (hω.om_pres (m, h) f hf)).2.1
  have hM1 : ∀ f', IsThetaFunO ψ V' W f' → IsThetaFunO ψ V' W (M f') := by
    intro f' hf'
    obtain ⟨f, hf, rfl⟩ := GlobalTheory.T.theta_restriction_down_witt_tower_surjective D V V' W r C B hs ψ hψ μ 𝓨 hcv f' hf'
    rw [hMres f hf]
    exact GlobalTheory.OrientedHeis.theta_smul _ (hω'.om_pres _ _ (hθω f hf))
  have hM2 : ∀ x f', IsThetaFunO ψ V' W f' → M (heisO ψ V' W x f') = heisO ψ V' W x (M f') := by
    intro x f' hf'
    obtain ⟨f, hf, rfl⟩ := GlobalTheory.T.theta_restriction_down_witt_tower_surjective D V V' W r C B hs ψ hψ μ 𝓨 hcv f' hf'
    have hx : heisO ψ V' W x (res V V' W C B μ 𝓨 f) =
        res V V' W C B μ 𝓨 (heisO ψ V W (midPart V V' W B x) f) :=
      (GlobalTheory.TowerRestrict.res_heis_mid hs μ 𝓨 f x).symm
    rw [hx, hMres _ (hheis _ _ hf), hMres f hf, hω.om_heis m h _ f hf, actO_midPart V V' W B g' m hB h x,
      GlobalTheory.TowerRestrict.res_heis_mid hs, hω'.om_heis _ _ _ _ (hθω f hf), actO_inv_actO, heisO_smul]
  have hM3 : ∀ (μ₀ : Measure (WO V' W)) (𝓕₀ : Set (WO V' W)), μ₀.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratL W V') 𝓕₀ μ₀ → ∀ f', IsThetaFunO ψ V' W f' →
      ∫⁻ w in 𝓕₀, ‖M f' w‖ₑ ^ 2 ∂μ₀ = ∫⁻ w in 𝓕₀, ‖f' w‖ₑ ^ 2 ∂μ₀ := by
    intro μ₀ 𝓕₀ hH hF f' hf'
    obtain ⟨f, hf, rfl⟩ := GlobalTheory.T.theta_restriction_down_witt_tower_surjective D V V' W r C B hs ψ hψ μ 𝓨 hcv f' hf'
    rw [hMres f hf]
    have hpt : ∀ w, ‖(d⁻¹ • ω' (g'⁻¹, h⁻¹) (res V V' W C B μ 𝓨 (ω (m, h) f))) w‖ₑ ^ 2 =
        ‖d⁻¹‖ₑ ^ 2 * ‖ω' (g'⁻¹, h⁻¹) (res V V' W C B μ 𝓨 (ω (m, h) f)) w‖ₑ ^ 2 := by
      intro w
      rw [Pi.smul_apply, smul_eq_mul, enorm_mul, mul_pow]
    simp only [hpt]
    rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top enorm_ne_top),
      hω'.om_unit μ₀ 𝓕₀ hH hF _ _ (hθω f hf),
      GlobalTheory.T.leviElement_scales_restrictionNormSq_absDet D V V' W r C B hs ψ χS χT ω hω μ 𝓨 hcv μ₀ 𝓕₀ hH hF a g' m hC hB h f hf,
      ← mul_assoc, enorm_inv_detPow_sq, one_mul]
  obtain ⟨c₀, hc₀, hM⟩ := GlobalTheory.ThetaSchur.schur D ψ hψ V' W M hM1 hM2 hM3
  have hinv : ∀ X, ω' (g', h) (ω' (g'⁻¹, h⁻¹) X) = X := by
    intro X
    have e : ω' (g', h) * ω' (g'⁻¹, h⁻¹) = 1 := by
      rw [← map_mul]
      show ω' ((g', h) * (g', h)⁻¹) = 1
      rw [mul_inv_cancel, map_one]
    exact congrArg (fun L : Module.End ℂ (WO V' W → ℂ) => L X) e
  refine ⟨⟨c₀, mem_sphere_zero_iff_norm.2 hc₀⟩, fun f hf => ?_⟩
  have e2 : d⁻¹ • ω' (g'⁻¹, h⁻¹) (res V V' W C B μ 𝓨 (ω (m, h) f)) = c₀ • res V V' W C B μ 𝓨 f := by
    rw [← hMres f hf]
    exact hM _ (hres.1 f hf).2.1
  have e3 : d⁻¹ • res V V' W C B μ 𝓨 (ω (m, h) f) = c₀ • ω' (g', h) (res V V' W C B μ 𝓨 f) := by
    have e4 := congrArg (ω' (g', h)) e2
    rwa [map_smul, map_smul, hinv] at e4
  calc res V V' W C B μ 𝓨 (ω (m, h) f) = d • (d⁻¹ • res V V' W C B μ 𝓨 (ω (m, h) f)) := by
        rw [smul_smul, mul_inv_cancel₀ hd0, one_smul]
    _ = _ := by
        rw [e3, smul_smul]
        congr 1
        exact mul_comm _ _

end GlobalTheory.LeviScalar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictionWittTowerIntertwinesLeviWeilRepStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restriction_wittTower_intertwines_levi_weilRep : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (χS' χT' : (AE D)ˣ →* Circle) (ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)), IsWeilDatumO ψ V' W χS' χT' ω' → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ (a : GL (Fin r) (AE D)) (g' : GA D V') (m : GA D V), HMul.hMul (Formalism.L2.Theta.mt V m) (C.map (incA D)) = HMul.hMul (C.map (incA D)) a.val → HMul.hMul (Formalism.L2.Theta.mt V m) (B.map (incA D)) = HMul.hMul (B.map (incA D)) (Formalism.L2.Theta.mt V' g') → ∀ h : GA D W, ∃ c : Circle, ∀ f, IsThetaFunO ψ V W f → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (m, h) f) = ((c : ℂ) * (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a W.rank : ℂ)) • ω' (g', h) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f) := by
  first | exact @GlobalTheory.LeviScalar.main | exact GlobalTheory.LeviScalar.main | (intros; apply GlobalTheory.LeviScalar.main <;> assumption)
end
