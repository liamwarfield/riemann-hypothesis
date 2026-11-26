module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSiegelWeilSectionMemDegeneratePrincipalS
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiActionTargetFlagUnipotentHomEquivariant
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IkedaMapSchrodingerPartialIntegral
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNsmulMemStdHom
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StrongApproximationDecomposition
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentSubMulComplementEqComplement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleMixedModelBaseValueEquivariant
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleMixedModelBaseValueEquivariant
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
namespace GlobalTheory.EvalAtZero

variable {D : D7}

theorem heisO_smul (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w₀ : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T w₀ (c • f) = c • heisO ψ S T w₀ f := by
  funext w
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem det_UX {ρ : ℕ} (γ : UX D ρ) : Matrix.GeneralLinearGroup.det γ.1 = 1 := by
  have hu : γ.1 ∈ UX D ρ := γ.2
  rw [mem_UX] at hu
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
  have hT : (γ.1.1 : Matrix (Fin ρ) (Fin ρ) (AE D)).BlockTriangular id := fun i j hij => (hu i j).1 hij
  rw [Matrix.det_of_upperTriangular hT]
  exact Finset.prod_eq_one fun i _ => (hu i i).2

end GlobalTheory.EvalAtZero

namespace GlobalTheory.EvalAtZero

theorem halfMod_UX {D : D7} {ρ : ℕ} (n : ℕ) (γ : UX D ρ) : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod n γ.1 = 1 := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod, det_UX, map_one, NNReal.coe_one, Real.one_rpow]

end GlobalTheory.EvalAtZero


open GlobalTheory.EvalAtZero in
theorem GlobalTheory.Unf.evalAt_xZero_yZero_rad : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (om' : Om B.V₀ J.W), IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om' → ∀ (Ψ : WO B.V J.W → ℂ), IsThetaFunO ψ B.V J.W Ψ → ∀ (u : UX D ρ) h₀, ∀ n ∈ radX J.d, ∀ h', evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (embA B.d B.o h₀, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) = s.om₀ (B.o.emb (h₀, 1), 1) (opA ψ J.d B.o B.ζ s.om₀ n h' (evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)))) := by
  intro D ψ ρ B J s om' hom' Ψ hΨ
  have FS := fun f hf => GlobalTheory.T.mixedModelFormulasWittSource_proof D ψ B.V B.V₀ J.W ρ B.d s.χV s.χW s.om om' s.weil hom' s.vS.μ s.vS.𝓕 s.vS.covol f hf
  have FT := fun f hf => GlobalTheory.T.mixedModelFormulas_wittTarget D ψ B.V₀ J.W J.W₀ ρ J.d s.χV s.χW om' s.om₀ hom' s.weil₀ s.vT.μ s.vT.𝓕 s.vT.covol f hf
  have MV := fun x => (GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions D ψ s.weil.std).1 B.V B.V₀ J.W ρ B.d s.vS.μ s.vS.𝓕 s.vS.covol Ψ hΨ x
  set y₀ := yZero B.V₀ ρ (vecB B.o B.ζ) with hy₀
  intro u h₀ n hn h'
  obtain ⟨b, c, rfl⟩ := ((GlobalTheory.MixPer.flag_jacobi_structure D J.W J.W₀ ρ J.d).2.1 n).1 hn
  set k := J.d.nB b * J.d.nC c * J.d.emb0 h' with hk
  have hks : k ∈ stabX J.d := mul_mem (radX_le_stabX J.d hn) (wittSmallGroupEmbedding_mem_pointwiseStabilizerIsotropic J.d h')
  have hkx : mt J.W k⁻¹ ⬝ J.d.jX = J.d.jX := inv_mem hks

  have e1 : (embA B.d B.o h₀, k) = (embA B.d B.o h₀, 1) * (1, k) := Prod.ext (mul_one _).symm (one_mul _).symm
  have hk1 := s.weil.om_pres (1, k) Ψ hΨ
  have s1 : B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 (s.om (embA B.d B.o h₀, k) Ψ) (xZero J.d ⬝ u.1.1) =
      om' (B.o.emb (h₀, 1), 1) (om' (1, k) (B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 Ψ (xZero J.d ⬝ u.1.1))) := by
    have hc := (FS _ hk1).core (B.o.emb (h₀, 1)) (xZero J.d ⬝ u.1.1)
    have ht := (FS _ hΨ).target k (xZero J.d ⬝ u.1.1)
    change B.d.mixS _ _ _ _ _ _ = _ at hc
    rw [e1, map_mul, Module.End.mul_apply, embA_apply, hc, ht, ← Matrix.mul_assoc,
      xZero, hkx]
    rfl
  set G := B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 Ψ (xZero J.d ⬝ u.1.1) with hG
  have hGt : IsThetaFunO ψ B.V₀ J.W G := MV _

  have e2 : ((1 : GA D B.V₀), k) = (1, J.d.nB b) * ((1, J.d.nC c) * (1, J.d.emb0 h')) :=
    Prod.ext (by rw [Prod.fst_mul, Prod.fst_mul, mul_one, mul_one]) (by rw [Prod.snd_mul, Prod.snd_mul, hk, mul_assoc])
  have h3 := hom'.om_pres (1, J.d.emb0 h') G hGt
  have h2 := hom'.om_pres (1, J.d.nC c) _ h3
  have hy : mt B.V₀ (B.o.emb (h₀, 1))⁻¹ ⬝ y₀ = y₀ := by
    rw [hy₀, yZero_vecB, ← map_inv, Prod.inv_mk, inv_one, ← Matrix.mul_assoc, B.o.emb_jB, mt_one, Matrix.mul_one]
  have hpt : ptT J.d B.V₀ y₀ (J.d.nB b * J.d.nC c) = GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj B.V₀ J.W₀ (y₀ ⬝ b) := by
    rw [ptT_nB_mul_nC, ← ptT_nB_mul_nC J.d B.V₀ y₀ b 0, J.d.nC_zero, mul_one, ptT,
      GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.wittSmallProjection_wittNB_inv_mul_adjointInclusion]
  have hcen : cenT J.d B.V₀ y₀ (J.d.nB b * J.d.nC c) = J.d.qT B.V₀ c y₀ :=
    (GlobalTheory.T.jacobi_action_target_flag_unipotent_hom_equivariant D ψ J.W J.W₀ B.V₀ ρ J.d y₀ (fun v hv => yZero_mul B.V₀ _ hv)).1 b c
  have t1 := (FT _ hGt).core h' y₀
  have t2 := (FT _ h3).centre c y₀
  have t3 := (FT _ h2).unip b y₀
  have t4 := (FT _ (hom'.om_pres (1, k) G hGt)).source (B.o.emb (h₀, 1)) y₀
  have t5 : om' (1, k) G = om' (1, J.d.nB b) (om' (1, J.d.nC c) (om' (1, J.d.emb0 h') G)) := by
    rw [e2, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  change (_root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.target J.d) B.V₀ ψ s.vT.μ s.vT.𝓕 (B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 (s.om (embA B.d B.o h₀, k) Ψ) (xZero J.d ⬝ u.1.1)) y₀ = _
  rw [s1, t4, hy, t5, t3, t2, t1]
  show _ = s.om₀ (B.o.emb (h₀, 1), 1) (jacT ψ J.d B.V₀ y₀ (J.d.nB b * J.d.nC c) (s.om₀ (1, h') _))
  unfold jacT
  simp only [hpt, hcen, heisO_smul, evalAt, hG]
  rfl


open GlobalTheory.EvalAtZero in
theorem GlobalTheory.Unf.evalAt_xZero_yZero_levi : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (om' : Om B.V₀ J.W), IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om' → ∀ (Ψ : WO B.V J.W → ℂ), IsThetaFunO ψ B.V J.W Ψ → ∀ (u γ : UX D ρ), evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, J.d.levi γ.1) Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) = evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ (γ⁻¹ * u).1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) := by
  intro D ψ ρ B J s om' hom' Ψ hΨ
  have FS := fun f hf => GlobalTheory.T.mixedModelFormulasWittSource_proof D ψ B.V B.V₀ J.W ρ B.d s.χV s.χW s.om om' s.weil hom' s.vS.μ s.vS.𝓕 s.vS.covol f hf
  have FT := fun f hf => GlobalTheory.T.mixedModelFormulas_wittTarget D ψ B.V₀ J.W J.W₀ ρ J.d s.χV s.χW om' s.om₀ hom' s.weil₀ s.vT.μ s.vT.𝓕 s.vT.covol f hf
  have MV := fun x => (GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions D ψ s.weil.std).1 B.V B.V₀ J.W ρ B.d s.vS.μ s.vS.𝓕 s.vS.covol Ψ hΨ x
  set y₀ := yZero B.V₀ ρ (vecB B.o B.ζ) with hy₀
  intro u γ
  have e0 : (mt J.W (J.d.levi γ.1)⁻¹ ⬝ (xZero J.d ⬝ u.1.1) : Mx D J.W.rank ρ) = xZero J.d ⬝ (γ⁻¹ * u).1.1 := by
    rw [← map_inv, ← Matrix.mul_assoc, levi_xZero, Matrix.mul_assoc, Subgroup.coe_mul, Subgroup.coe_inv,
      Units.val_mul]
  change (_root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.target J.d) B.V₀ ψ s.vT.μ s.vT.𝓕 ((_root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.source B.d) J.W ψ s.vS.μ s.vS.𝓕 (s.om (1, J.d.levi γ.1) Ψ) (xZero J.d ⬝ u.1.1)) y₀ = _
  rw [(FS _ hΨ).target, e0, (FT _ (MV _)).levi, yZero_mul B.V₀ _ γ.2, det_UX, halfMod_UX, map_one,
    Circle.coe_one, Complex.ofReal_one, mul_one, one_smul]
  rfl

theorem GlobalTheory.Unf.evalAt_xZero_yZero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (om' : Om B.V₀ J.W), IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om' → ∀ (Ψ : WO B.V J.W → ℂ), IsThetaFunO ψ B.V J.W Ψ → (∀ (u : UX D ρ) h₀, ∀ n ∈ radX J.d, ∀ h', evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (embA B.d B.o h₀, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) = s.om₀ (B.o.emb (h₀, 1), 1) (opA ψ J.d B.o B.ζ s.om₀ n h' (evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ))))) ∧ ∀ (u γ : UX D ρ), evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, J.d.levi γ.1) Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) = evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ (γ⁻¹ * u).1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) :=
  fun D ψ ρ B J s om' hom' Ψ hΨ => ⟨GlobalTheory.Unf.evalAt_xZero_yZero_rad D ψ ρ B J s om' hom' Ψ hΨ,
    GlobalTheory.Unf.evalAt_xZero_yZero_levi D ψ ρ B J s om' hom' Ψ hΨ⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleMixedModelBaseValueEquivariantStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleMixedModel_baseValue_equivariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (om' : Om B.V₀ J.W), IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om' → ∀ (Ψ : WO B.V J.W → ℂ), IsThetaFunO ψ B.V J.W Ψ → (∀ (u : UX D ρ) h₀, ∀ n ∈ radX J.d, ∀ h', evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (embA B.d B.o h₀, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) = s.om₀ (B.o.emb (h₀, 1), 1) (opA ψ J.d B.o B.ζ s.om₀ n h' (evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ))))) ∧ ∀ (u γ : UX D ρ), evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, J.d.levi γ.1) Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) = evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ (γ⁻¹ * u).1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) := by
  first | exact @GlobalTheory.Unf.evalAt_xZero_yZero | exact GlobalTheory.Unf.evalAt_xZero_yZero | (intros; apply GlobalTheory.Unf.evalAt_xZero_yZero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IkedaMapSchrodingerPartialIntegralStatement
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ikedaMap_schrodinger_partialIntegral : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A T T' : HSp D) (t : ℕ) (d : HypDec T T' t) (ν : Measure (WO A T)) (𝓨 : Set (WO A T)), IsCovolOne (ratL T A) ν 𝓨 → ∀ (ν' : Measure (WO A T')) (𝓨' : Set (WO A T')), IsCovolOne (ratL T' A) ν' 𝓨' → ∀ (μ₁ : Measure (Mx D t (dblSp A).rank)) (𝓕₁ : Set (Mx D t (dblSp A).rank)), IsCovolOne (ratMx D t (dblSp A).rank) μ₁ 𝓕₁ → ∀ (μ₂ : Measure (Mx D t A.rank)) (𝓕₂ : Set (Mx D t A.rank)), IsCovolOne (ratMx D t A.rank) μ₂ 𝓕₂ → ∀ φ, IsThetaFunO ψ (dblSp A) T φ → IsThetaFunO ψ (dblSp A) T' (ikeda ψ d μ₁ 𝓕₁ φ) ∧ sch ψ A T' ν' 𝓨' (ikeda ψ d μ₁ 𝓕₁ φ) = ikS d μ₂ (sch ψ A T ν 𝓨 φ) := by
  first | exact @GlobalTheory.IkedaSch.sch_ikeda | exact GlobalTheory.IkedaSch.sch_ikeda | (intros; apply GlobalTheory.IkedaSch.sch_ikeda <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjPEqCP
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.OffIdemDen
open GlobalTheory.IdemSupport

variable {D : D7}

theorem cP_cP (P : HeightOneSpectrum (𝓞 D.host.E)) : cP (cP P) = P :=
  HeightOneSpectrum.ext (Ideal.ext fun x => by rw [mem_cP, mem_cP, cO_cO])

theorem conjP_eq_cP (Q : HeightOneSpectrum (𝓞 D.host.E)) : Formalism.L2.Col.conjPrime₂ Q = cP Q :=
  HeightOneSpectrum.ext (Ideal.ext fun _ => Iff.rfl)

def evQ (Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    AE D →+* Q.adicCompletion D.host.E where
  toFun z := Φ z Q
  map_one' := by rw [map_one]; rfl
  map_mul' a b := ev_mul a b Q
  map_zero' := ev_zero Q
  map_add' a b := ev_add a b Q

theorem delta_mem {Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E} {P : HeightOneSpectrum (𝓞 D.host.E)}
    {x : AE D} (h : IsDelta Φ P x) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    Φ x Q ∈ Q.adicCompletionIntegers D.host.E := by
  by_cases hQ : Q = P
  · subst hQ; rw [h.2.1]; exact (Q.adicCompletionIntegers D.host.E).one_mem
  · rw [h.2.2 Q hQ]; exact (Q.adicCompletionIntegers D.host.E).zero_mem

end GlobalTheory.OffIdemDen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymplOHEqZeroOfHO
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IdemSumVac

variable {D : D7}

theorem symplOH_eq_zero_of_hO {S T : HSp D} {u u' : WO S T} (h : hO S T u u' = 0) : symplOH S T u u' = 0 := by
  rw [symplOH, symplO, h, mul_zero, map_zero, mul_zero]

theorem heisO_sum_smul (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) (f : WO S T → ℂ)
    (hf : IsLatVac (heisO ψ S T) Λ f) (hΛ : ∀ w : AE D, finPart D w ∈ intAE D → ∀ u ∈ Λ, w • u ∈ Λ)
    {ι : Type} (p : ι → AE D) (s : Finset ι) (hs : ∀ i ∈ s, IsSplitIdem D (p i))
    (hc : ∀ i ∈ s, ∀ j ∈ s, p i * cA D (p j) = 0) (x : WO S T) (hx : x ∈ Λ) :
    heisO ψ S T ((∑ i ∈ s, p i) • x) f = f := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, zero_smul]; exact GlobalTheory.LatVac.heisO_zero ψ f
  | insert a s ha ih =>
    have hsa := hs a (Finset.mem_insert_self _ _)
    have ih' := ih (fun i hi => hs i (Finset.mem_insert_of_mem hi))
      (fun i hi j hj => hc i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))
    have hmem : p a • x ∈ Λ := hΛ _ (GlobalTheory.SplitHomLattice.idem_int hsa) x hx
    have hhalf : IsHalf (p a) (p a • x) := fun i j => by
      rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hsa.1]
    have h1 : heisO ψ S T (p a • x) f = f := hf.2 (p a) hsa _ hmem hhalf
    have hz : hO S T (p a • x) ((∑ i ∈ s, p i) • x) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [GlobalTheory.LatVacSign.hO_smul_smul, map_sum, Finset.mul_sum,
        Finset.sum_eq_zero (fun j hj => hc a (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)),
        zero_mul]
    have key := GlobalTheory.LatVac.heisO_heisO ψ (p a • x) ((∑ i ∈ s, p i) • x) f
    rw [ih', h1, symplOH_eq_zero_of_hO hz, ψ.map_zero_eq_one, one_smul, ← add_smul] at key
    rw [Finset.sum_insert ha]
    exact key.symm

theorem isSplitIdem_cA {e : AE D} (he : IsSplitIdem D e) : IsSplitIdem D (cA D e) := by
  obtain ⟨he1, he2, v, ε, hpl, he3⟩ := he
  exact ⟨by rw [← RingHom.map_mul, he1], by rw [GlobalTheory.LatVac.cA_cA, mul_comm, he2], v, ε, hpl,
    by rw [GlobalTheory.LatVac.cA_cA, add_comm, he3]⟩

theorem heisO_idemSum_fix : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T))
    (f : WO S T → ℂ), IsLatVac (heisO ψ S T) Λ f → (∀ w : AE D, finPart D w ∈ intAE D → ∀ u ∈ Λ, w • u ∈ Λ) →
    ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ x ∈ Λ,
      heisO ψ S T (e • x) f = f ∧ heisO ψ S T (cA D e • x) f = f := by
  intro D ψ S T Λ f hf hΛ e SS he x hx
  obtain ⟨⟨es, hes, rfl⟩, hce⟩ := he
  have h1 : ∀ i ∈ SS, es i * es i = es i := fun i hi => (hes i hi).1.1
  have hcross : ∀ i ∈ SS, ∀ j ∈ SS, es i * cA D (es j) = 0 :=
    GlobalTheory.PlaceDatum.cross_eq_zero (R := AE D) GlobalTheory.PlaceDatum.isUnit_natCast (cA D) es SS h1 hce
  refine ⟨heisO_sum_smul ψ S T Λ f hf hΛ es SS (fun i hi => (hes i hi).1) hcross x hx, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine heisO_sum_smul ψ S T Λ f hf hΛ (fun i => cA D (es i)) SS (fun i hi => isSplitIdem_cA (hes i hi).1)
    (fun i hi j hj => ?_) x hx
  rw [← RingHom.map_mul, hcross i hi j hj, map_zero]

end GlobalTheory.IdemSumVac
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CarriesLatticeCompletionOfEachPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CarriesLatticeCompletionOfEachPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.MovesPl

open GlobalTheory.FinPl GlobalTheory.FinPl.KSplit GlobalTheory.FinPl.KOpen

variable {D : D7}

theorem latV_transfer (S : HSp D) (L : Lat S) {P₁ P₂ : Pl D → Prop} (h : ∀ p, P₁ p → P₂ p)
    {z : Fin S.rank → AE D} (hz : ∀ i, z i ∈ idAt D P₁) : z ∈ latV S L P₁ ↔ z ∈ latV S L P₂ := by
  rw [mem_latV_iff S L P₁ z hz, mem_latV_iff S L P₂ z fun i => idAt_mono h (hz i)]

theorem mem_latV_empty (S : HSp D) (L : Lat S) {z : Fin S.rank → AE D}
    (hz : ∀ i, z i ∈ idAt D (· ∈ (∅ : Finset (Pl D)))) : z ∈ latV S L (· ∈ (∅ : Finset (Pl D))) := by
  classical
  rw [mem_latV_iff S L _ z hz]
  have h0 : finPart D ∘ z = 0 := by
    funext i
    rw [Function.comp_apply, ← e_mul_fin (hz i)]
    refine GlobalTheory.LatticeLocalGlobal.ext_components _ _ fun w => ?_
    change GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w _ = GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w _
    rw [map_mul, compFin_e, if_neg (Finset.notMem_empty w), zero_mul, Pi.zero_apply, map_zero]
  rw [h0]
  exact zero_mem _

theorem moves_of_places : ∀ {D : D7} (S : HSp D) (g : GA D S) (L M : Lat S) (Q : Finset (Pl D)),
    (∀ v ∈ Q, Moves S g L M (· = v)) → Moves S g L M (· ∈ Q) := by
  intro D S g L M Q
  classical
  induction Q using Finset.induction_on with
  | empty =>
    intro _ y hy
    exact iff_of_true (mem_latV_empty S L hy) (mem_latV_empty S M (supp_mulVec S _ g hy))
  | insert v Q hv ih =>
    intro hQ y hy
    have hQ' := ih fun w hw => hQ w (Finset.mem_insert_of_mem hw)
    have hvv := hQ v (Finset.mem_insert_self v Q)
    have hgy := supp_mulVec S _ g hy
    have comm : ∀ c : AE D, c • (mt S g *ᵥ y) = mt S g *ᵥ (c • y) := fun c => (mulVec_smul _ _ _).symm
    have s1 : ∀ i, (eQ {v} • y) i ∈ idAt D (fun p => p ∈ insert v Q ∧ p ∈ ({v} : Finset (Pl D))) :=
      fun i => mul_mem_idAt (eQ_off {v}) (hy i)
    have s2 : ∀ i, ((1 - eQ {v}) • y) i ∈ idAt D (fun p => p ∈ insert v Q ∧ p ∉ ({v} : Finset (Pl D))) :=
      fun i => mul_mem_idAt (one_sub_eQ_off {v}) (hy i)
    have i1 : ∀ p, (p ∈ insert v Q ∧ p ∈ ({v} : Finset (Pl D))) → p = v := fun p h => Finset.mem_singleton.1 h.2
    have i2 : ∀ p, (p ∈ insert v Q ∧ p ∉ ({v} : Finset (Pl D))) → p ∈ Q := fun p h =>
      (Finset.mem_insert.1 h.1).resolve_left fun e => h.2 (Finset.mem_singleton.2 e)
    have t1 : ∀ i, (eQ {v} • y) i ∈ idAt D (· = v) := fun i => idAt_mono i1 (s1 i)
    have t2 : ∀ i, ((1 - eQ {v}) • y) i ∈ idAt D (· ∈ Q) := fun i => idAt_mono i2 (s2 i)
    rw [mem_latV_iff_parts S L _ {v} hy, mem_latV_iff_parts S M _ {v} hgy, comm, comm,
      latV_transfer S L i1 s1, latV_transfer S L i2 s2,
      latV_transfer S M i1 (fun i => by rw [← comm]; exact mul_mem_idAt (eQ_off {v}) (hgy i)),
      latV_transfer S M i2 (fun i => by rw [← comm]; exact mul_mem_idAt (one_sub_eQ_off {v}) (hgy i))]
    exact and_congr (hvv _ t1) (hQ' _ t2)

end GlobalTheory.FinPl.MovesPl

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CarriesLatticeCompletionOfEachPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carriesLatticeCompletion_of_each_place : ∀ {D : D7} (S : HSp D) (g : GA D S) (L M : GlobalTheory.FinPl.Lat S) (Q : Finset (GlobalTheory.FinPl.Pl D)), (∀ v ∈ Q, GlobalTheory.FinPl.Moves S g L M (· = v)) → GlobalTheory.FinPl.Moves S g L M (· ∈ Q) := by
  first | exact @GlobalTheory.FinPl.MovesPl.moves_of_places | exact GlobalTheory.FinPl.MovesPl.moves_of_places | (intros; apply GlobalTheory.FinPl.MovesPl.moves_of_places <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSupportAconvPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.QVal GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.QValOuter

open AddMonoidAlgebra in
theorem aconv_cons {G : Type} [AddMonoid G] (e : G →₀ ℂ) (l : List (G →₀ ℂ)) :
    (ofCoeff (aconv (e :: l)) : AddMonoidAlgebra ℂ G) = ofCoeff e * ofCoeff (aconv l) := by
  apply AddMonoidAlgebra.coeff_injective
  rw [AddMonoidAlgebra.mul_def, AddMonoidAlgebra.coeff_finsuppSum]
  simp only [AddMonoidAlgebra.coeff_finsuppSum, AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_ofCoeff]
  rfl

theorem aconv_nil {G : Type} [AddMonoid G] :
    (AddMonoidAlgebra.ofCoeff (aconv ([] : List (G →₀ ℂ))) : AddMonoidAlgebra ℂ G) = 1 := rfl

theorem aconv_pair {G : Type} [AddMonoid G] (c d : G →₀ ℂ) :
    (AddMonoidAlgebra.ofCoeff (aconv [c, d]) : AddMonoidAlgebra ℂ G) =
      AddMonoidAlgebra.ofCoeff c * AddMonoidAlgebra.ofCoeff d := by
  rw [aconv_cons, aconv_cons, aconv_nil, mul_one]

theorem aconv_pair_cons {G : Type} [AddMonoid G] (c d : G →₀ ℂ) (l : List (G →₀ ℂ)) :
    aconv (aconv [c, d] :: l) = aconv (c :: d :: l) := by
  apply (AddMonoidAlgebra.ofCoeff_injective (R := ℂ) (M := G))
  rw [aconv_cons, aconv_pair, aconv_cons, aconv_cons, mul_assoc]

theorem mem_support_aconv_pair {G : Type} [AddMonoid G] (c d : G →₀ ℂ) {u : G} (hu : u ∈ (aconv [c, d]).support) :
    ∃ a ∈ c.support, ∃ b ∈ d.support, a + b = u := by
  classical
  have h : (AddMonoidAlgebra.ofCoeff c * AddMonoidAlgebra.ofCoeff d : AddMonoidAlgebra ℂ G).coeff u ≠ 0 := by
    rw [← aconv_pair]; exact Finsupp.mem_support_iff.1 hu
  rw [AddMonoidAlgebra.coeff_mul] at h
  simp only [AddMonoidAlgebra.coeff_ofCoeff] at h
  obtain ⟨a, ha, h1⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨b, hb, h2⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  by_cases hab : a + b = u
  · exact ⟨a, ha, b, hb, hab⟩
  · exact absurd (if_neg hab) h2

open MonoidAlgebra in
theorem conv_cons {G : Type} [Monoid G] (e : G →₀ ℂ) (l : List (G →₀ ℂ)) :
    (ofCoeff (conv (e :: l)) : MonoidAlgebra ℂ G) = ofCoeff e * ofCoeff (conv l) := by
  apply MonoidAlgebra.coeff_injective
  rw [MonoidAlgebra.mul_def, MonoidAlgebra.coeff_finsuppSum]
  simp only [MonoidAlgebra.coeff_finsuppSum, MonoidAlgebra.coeff_single, MonoidAlgebra.coeff_ofCoeff]
  rfl

theorem conv_nil {G : Type} [Monoid G] :
    (MonoidAlgebra.ofCoeff (conv ([] : List (G →₀ ℂ))) : MonoidAlgebra ℂ G) = 1 := rfl

theorem mul_comm_of_support {G : Type} [Monoid G] (a b : MonoidAlgebra ℂ G)
    (h : ∀ x ∈ a.coeff.support, ∀ y ∈ b.coeff.support, x * y = y * x) : a * b = b * a := by
  rw [MonoidAlgebra.mul_def, MonoidAlgebra.mul_def]
  unfold Finsupp.sum
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y hy => Finset.sum_congr rfl fun x hx => ?_
  dsimp only
  rw [h x hx y hy, mul_comm (a.coeff x)]

theorem comm_conv {G : Type} [Monoid G] (E : G →₀ ℂ) (l : List (G →₀ ℂ))
    (h : ∀ x ∈ E.support, ∀ e ∈ l, ∀ y ∈ e.support, x * y = y * x) :
    (MonoidAlgebra.ofCoeff E : MonoidAlgebra ℂ G) * MonoidAlgebra.ofCoeff (conv l) =
      MonoidAlgebra.ofCoeff (conv l) * MonoidAlgebra.ofCoeff E := by
  induction l with
  | nil => rw [conv_nil, mul_one, one_mul]
  | cons e l ih =>
    have h1 : (MonoidAlgebra.ofCoeff E : MonoidAlgebra ℂ G) * MonoidAlgebra.ofCoeff e =
        MonoidAlgebra.ofCoeff e * MonoidAlgebra.ofCoeff E :=
      mul_comm_of_support _ _ fun x hx y hy => h x hx e List.mem_cons_self y hy
    rw [conv_cons, ← mul_assoc, h1, mul_assoc, ih fun x hx e' he' y hy => h x hx e' (List.mem_cons_of_mem _ he') y hy,
      mul_assoc]

section Trc
variable {D : D7} {V : HSp D}

theorem trc_eq_sum (e : GA D V →₀ ℂ) (f : GA D V → ℂ) : trc e f = e.sum fun g a => a • rTrans g f := rfl

theorem trc_single (g : GA D V) (a : ℂ) (f : GA D V → ℂ) : trc (Finsupp.single g a) f = a • rTrans g f := by
  rw [trc_eq_sum, Finsupp.sum_single_index]
  exact zero_smul _ _

theorem trc_zero (f : GA D V → ℂ) : trc (0 : GA D V →₀ ℂ) f = 0 := by
  simp [trc]

theorem trc_add (e e' : GA D V →₀ ℂ) (f : GA D V → ℂ) : trc (e + e') f = trc e f + trc e' f := by
  simp only [trc_eq_sum]
  exact Finsupp.sum_add_index' (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)

theorem trc_apply (e : GA D V →₀ ℂ) (f : GA D V → ℂ) (x : GA D V) : trc e f x = ∑ g ∈ e.support, e g * f (x * g) := by
  simp [trc, Finset.sum_apply, rTrans]

theorem trc_add_right (e : GA D V →₀ ℂ) (f f' : GA D V → ℂ) : trc e (f + f') = trc e f + trc e f' := by
  funext x
  simp only [trc_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem trc_zero_right (e : GA D V →₀ ℂ) : trc e (0 : GA D V → ℂ) = 0 := by
  funext x
  simp [trc_apply]

theorem trc_mul (e e' : GA D V →₀ ℂ) (f : GA D V → ℂ) :
    trc (MonoidAlgebra.ofCoeff e * MonoidAlgebra.ofCoeff e' : MonoidAlgebra ℂ (GA D V)).coeff f = trc e (trc e' f) := by
  induction e using Finsupp.induction_linear with
  | zero => rw [MonoidAlgebra.ofCoeff_zero, zero_mul, MonoidAlgebra.coeff_zero, trc_zero, trc_zero]
  | add x y hx hy =>
    rw [MonoidAlgebra.ofCoeff_add, add_mul, MonoidAlgebra.coeff_add, trc_add, trc_add, hx, hy]
  | single g a =>
    induction e' using Finsupp.induction_linear with
    | zero => rw [MonoidAlgebra.ofCoeff_zero, mul_zero, MonoidAlgebra.coeff_zero, trc_zero, trc_zero_right]
    | add x y hx hy =>
      rw [MonoidAlgebra.ofCoeff_add, mul_add, MonoidAlgebra.coeff_add, trc_add, hx, hy, trc_add, trc_add_right]
    | single h b =>
      rw [MonoidAlgebra.ofCoeff_single, MonoidAlgebra.ofCoeff_single, MonoidAlgebra.single_mul_single,
        MonoidAlgebra.coeff_single, trc_single, trc_single, trc_single]
      funext x
      simp only [rTrans, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem contAut_trc (e : GA D V →₀ ℂ) {f : GA D V → ℂ} (hf : IsContAut V f) : IsContAut V (trc e f) := by
  refine ⟨fun γ hγ x => ?_, ?_⟩
  · simp only [trc_apply, mul_assoc, hf.1 γ hγ]
  · have : trc e f = fun x => ∑ g ∈ e.support, e g * f (x * g) := funext (trc_apply e f)
    rw [this]
    exact continuous_finsetSum _ fun g _ => (GlobalTheory.Core.Mi.BotPin.isContAut_rTrans g hf).2.const_smul (e g)

end Trc

end GlobalTheory.QValOuter
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LiftsCharOfResidueCharAtSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LiftsCharOfResidueCharAtSplitPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

noncomputable section

namespace GlobalTheory.ResLift

open GlobalTheory.AdelicU

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)}

def swapProj (φ : SplitProj D v) : D.host.E ⊗[D.host.F] Fv D.host.F v →+* Fv D.host.F v :=
  φ.toRingHom.comp (Algebra.TensorProduct.comm D.host.F D.host.E (Fv D.host.F v)).toAlgHom.toRingHom

theorem swapProj_one_tmul (φ : SplitProj D v) (a : Fv D.host.F v) : swapProj φ ((1 : D.host.E) ⊗ₜ[D.host.F] a) = a := by
  change φ (a ⊗ₜ[D.host.F] (1 : D.host.E)) = a
  exact φ.commutes a

theorem swapProj_prV (φ : SplitProj D v) (z : EAf D) : swapProj φ (Formalism.UG.prV v z) = GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul b y => rfl

theorem swapProj_prV_oToS (φ : SplitProj D v) (x : 𝓞 D.host.E) :
    swapProj φ (Formalism.UG.prV v (Formalism.L2.DIV.oToS D.host.F D.host.E x).1) = GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (x : D.host.E) := by
  rw [swapProj_prV, Formalism.L2.DIV.oToS_coe]
  change φ ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v 1) ⊗ₜ[D.host.F] (x : D.host.E)) = _
  rw [map_one]
  rfl

theorem isIdemOf_idem (φ : SplitProj D v) : IsIdemOf φ (GlobalTheory.EmbChart.idem (GlobalTheory.SplitProjChart.emb φ)) := by
  refine ⟨GlobalTheory.EmbChart.isSplitIdem_idem _, ?_, GlobalTheory.SplitProjChart.rdA_idem φ⟩
  rw [GlobalTheory.EmbChart.cA_idem, GlobalTheory.EmbChart.idem, ← LinearMap.map_add (f := _), add_sub_cancel]
  rfl

theorem eq_splitPrime {φ : SplitProj D v} {PP : Pl D.host.E} (hφ : IsProjAt φ PP) :
    PP = splitPrime (GlobalTheory.SplitProjChart.emb φ) :=
  HeightOneSpectrum.ext (Ideal.ext fun x => (hφ x).trans (mem_splitPrime (GlobalTheory.SplitProjChart.emb φ) x).symm)

theorem exists_mem_only (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : ∃ p ∈ (splitPrime τ).asIdeal,
    ∀ P : HeightOneSpectrum (𝓞 D.host.E), P.under (𝓞 D.host.F) = v → p ∈ P.asIdeal → P = splitPrime τ := by
  obtain ⟨p, hp, hp'⟩ : ∃ p ∈ (splitPrime τ).asIdeal, p ∉ (splitPrime (τ.comp D.sp.cm.sig)).asIdeal := by
    by_contra hc
    push Not at hc
    have h := (splitPrime τ).isMaximal.eq_of_le (splitPrime (τ.comp D.sp.cm.sig)).isPrime.ne_top hc
    exact splitPrime_comp_ne (isCMExt_host D) τ (HeightOneSpectrum.ext h.symm)
  refine ⟨p, hp, fun P hP hpP => ?_⟩
  have hm : P.asIdeal ∈ v.asIdeal.primesOver (𝓞 D.host.E) := ⟨P.isPrime, ⟨hP ▸ rfl⟩⟩
  rw [primesOver_eq_split (isCMExt_host D) τ] at hm
  rcases hm with h | h
  · exact HeightOneSpectrum.ext h
  · exact absurd (h ▸ hpP) hp'

theorem resS_eq {φ : SplitProj D v} {PP : Pl D.host.E} (hφ : IsProjAt φ PP)
    (s : Formalism.L2.Herm.intAf D.host.F D.host.E) (x : 𝓞 D.host.E)
    (h : Valued.v (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ s.1 - GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (x : D.host.E)) < 1) :
    resS D.host.F PP s = Ideal.Quotient.mk PP.asIdeal x := by
  obtain ⟨p, hp, hp'⟩ := exists_mem_only (GlobalTheory.SplitProjChart.emb φ)
  rw [← eq_splitPrime hφ] at hp hp'
  obtain ⟨ρ, ι, hρ, hρr⟩ := GlobalTheory.SplitResidue.exists_residue_equiv D.host.F D.host.E v PP
    (swapProj φ) p (swapProj_one_tmul φ) ((hφ p).1 hp) hp'
  have h0 : IsLocalRing.residue _ (ρ s) = IsLocalRing.residue _ (ρ (oToS D.host.F D.host.E x)) := by
    refine Ideal.Quotient.eq.2 ((GlobalTheory.SplitResidue.mem_maximalIdeal_iff v _).2 ?_)
    rw [AddSubgroupClass.coe_sub, hρ, hρ, swapProj_prV_oToS, swapProj_prV]
    exact h
  rw [hρr, hρr, resS_oToS] at h0
  exact ι.injective h0

theorem exists_unit_lift {A K : Type} [CommRing A] [CommRing K] (π : A →+* K) {e : A} (hee : e * e = e)
    (hs : Function.Surjective π) (hk : ∀ a, π a = 0 ↔ e * a = 0) (u : Kˣ) :
    ∃ x : Aˣ, (1 - e) * (x : A) = 1 - e ∧ e * ((x : A) - 1) = (x : A) - 1 ∧ π x = u := by
  obtain ⟨U, hU⟩ := hs (u : K)
  obtain ⟨U', hU'⟩ := hs ((u⁻¹ : Kˣ) : K)
  have h1 : e * (U * U' - 1) = 0 := (hk _).1 (by rw [map_sub, map_mul, hU, hU', map_one, Units.mul_inv, sub_self])
  have h2 : π (1 - e) = 0 := (hk _).2 (by linear_combination -hee)
  have h3 : π e = 1 := by
    rw [map_sub, map_one, sub_eq_zero] at h2
    exact h2.symm
  refine ⟨⟨e * U + (1 - e), e * U' + (1 - e), by linear_combination h1 + (U * U' - U - U' + 1) * hee,
    by linear_combination h1 + (U * U' - U - U' + 1) * hee⟩, ?_, ?_, ?_⟩
  · change (1 - e) * (e * U + (1 - e)) = 1 - e
    linear_combination (1 - U) * hee
  · change e * (e * U + (1 - e) - 1) = e * U + (1 - e) - 1
    linear_combination (U - 1) * hee
  · change π (e * U + (1 - e)) = u
    rw [map_add (f := _), map_mul, h2, h3, hU, one_mul, add_zero]

theorem liftsChar_of_resAt : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (PP : Pl D.host.E) (a : (kP PP)ˣ →* ℂˣ), GlobalTheory.StepLaw.ResAt χ PP a → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → ∀ μ : (Fv D.host.F v)ˣ →* ℂˣ, (∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μ y = Circle.toUnits (χ x)) → LiftsChar φ PP μ a := by
  intro D χ PP a hres v φ hφ μ hμ u k ⟨x0, hx0k, hx0⟩
  have he := isIdemOf_idem φ
  generalize GlobalTheory.EmbChart.idem (GlobalTheory.SplitProjChart.emb φ) = e at he
  have hch := (GlobalTheory.SplitProjChart.chart_rdA D v φ e he).1
  have hAt : Formalism.L2.NTheta.IsIdemAt e PP := (((GlobalTheory.SplitIdemDict.idem_dictionary D).2 v φ PP hφ).2.2 e he).1
  obtain ⟨x, h1, h2, h3⟩ := exists_unit_lift (rdA φ) he.1.1 hch.1 hch.2.1 u
  have hu : (u : Fv D.host.F v) ∈ v.adicCompletionIntegers D.host.F := by
    have h4 : (u : Fv D.host.F v) - GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (x0 : D.host.E) ∈ v.adicCompletionIntegers D.host.F := hx0.le
    have h5 : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (x0 : D.host.E) ∈ v.adicCompletionIntegers D.host.F :=
      apply_coe_mem (GlobalTheory.SplitProjChart.emb φ) x0
    have h6 := add_mem h4 h5
    rwa [sub_add_cancel] at h6
  have hint : toEAf D (x : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    have h4 : finPart D (e * ((x : AE D) - 1)) ∈ intAE D := by
      refine (hch.2.2.2 _).2 (GlobalTheory.SplitHecke.isInt_Ov.2 ?_)
      rw [RingHom.map_sub, h3, RingHom.map_one]
      exact sub_mem hu (one_mem _)
    have h5 := (GlobalTheory.SplitDec.int_iff _).1 h4
    rw [h2, RingHom.map_sub, RingHom.map_one] at h5
    have h6 := add_mem h5 (one_mem _)
    rwa [sub_add_cancel] at h6
  have hk : resS D.host.F PP ⟨_, hint⟩ = Ideal.Quotient.mk PP.asIdeal x0 := by
    refine resS_eq hφ _ x0 ?_
    change Valued.v (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ (toEAf D (x : AE D)) - _) < 1
    rw [GlobalTheory.SplitProjChart.rdE_toEAf, h3]
    exact hx0
  rw [hμ x u ⟨e, he, h1, h3⟩]
  exact Units.ext (hres e hAt x h2 hint k (hk.trans hx0k).symm)

end GlobalTheory.ResLift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LiftsCharOfResidueCharAtSplitPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftsChar_of_residueChar_at_splitPlace : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (PP : Pl D.host.E) (a : (kP PP)ˣ →* ℂˣ), GlobalTheory.StepLaw.ResAt χ PP a → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → ∀ μ : (Fv D.host.F v)ˣ →* ℂˣ, (∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μ y = Circle.toUnits (χ x)) → LiftsChar φ PP μ a := by
  first | exact @GlobalTheory.ResLift.liftsChar_of_resAt | exact GlobalTheory.ResLift.liftsChar_of_resAt | (intros; apply GlobalTheory.ResLift.liftsChar_of_resAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitPointWeilCharConductorOneOfUnits
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoreIffCollapsesWith
open MeasureTheory ValuativeRel Matrix
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
open scoped NNReal ENNReal

noncomputable section
namespace GlobalTheory.CollapseCompare

section Average
variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [AddCommGroup V] [Module ℂ V]

end Average

section Pointwise
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

variable [MeasurableSpace k] [BorelSpace k]

variable {ν : Measure k} {μX : Measure (GL n k)} {μG : Measure (GL (n ⊕ Fin c) k)}
  {J : Subgroup (GL (n ⊕ Fin c) k)} {bas : GL (n ⊕ Fin c) k} {ψ : AddChar k Circle} {μ : kˣ →* ℂˣ}
  {lam : J →* ℂˣ} {κ : ℝ}






end Pointwise

section Transport
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}





variable [MeasurableSpace k] [BorelSpace k]

end Transport

section Normalise
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
open GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical (frame)




theorem hasConductor_mulShift {ψ : AddChar k Circle} {β : kˣ} (h : HasConductor ψ β) :
    HasConductor (ψ.mulShift (β : k)) 1 := by
  have hβ : 0 < valuation k (β : k) := by simp [zero_lt_iff]
  intro x
  have h1 := h (β * x)
  rw [map_mul, mul_le_iff_le_one_right hβ] at h1
  rw [Units.val_one, map_one, ← h1]
  simp only [AddChar.mulShift_apply]
  refine ⟨fun H y hy => ?_, fun H y hy => H _ (by rw [map_mul]; exact mul_le_mul_right hy _)⟩
  have := H ((β⁻¹ : kˣ) * y) (by rwa [map_mul, Units.val_inv_eq_inv_val, map_inv₀, inv_mul_le_iff₀ hβ])
  simpa using this

variable [MeasurableSpace k] [BorelSpace k]

end Normalise

section Main

end Main

end GlobalTheory.CollapseCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitPointWeilCharConductorOneOfUnits
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

noncomputable section

namespace GlobalTheory.SplitWeilChar

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem splitPlace_polarisationDatum_inv_integral (q : SplitPt D k) (hU : q.UnitAA) : q.pr (incA D D.host.xi0⁻¹) ∈ 𝒪[k] := by
  obtain ⟨η, hη, h0, h⟩ := GlobalTheory.SplitCharCond.exists_idem q
  have hm : (pairA D.host.F 0 η ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) ∈ intAt D (· = q.v) := by
    refine ⟨⟨?_, ?_⟩, AddSubgroup.subset_closure ⟨η, hη, 1, rfl⟩⟩
    · change (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
      exact TensorProduct.zero_tmul _ _
    · refine Ideal.mem_iInf.2 fun w => ?_
      change evalV D.host.F w.1 η ⊗ₜ[D.host.F] (1 : D.host.E) = 0
      rw [h0 w.1 w.2, TensorProduct.zero_tmul]
  have := GlobalTheory.SplitCharCond.pr_int q (hU.1 _ hm).2.2
  rwa [map_mul, GlobalTheory.SplitCharCond.pr_pair_tmul q h, map_one, map_one, mul_one] at this

theorem valuation_pr_incA_xi0_eq_one_of_unitAA (q : SplitPt D k) (hU : q.UnitAA) : valuation k (q.pr (incA D D.host.xi0)) = 1 := by
  have h1 := (Valuation.mem_integer_iff _ _).1 (GlobalTheory.SplitCharCond.xi_zero_projection_integral q hU)
  have h2 := (Valuation.mem_integer_iff _ _).1 (splitPlace_polarisationDatum_inv_integral q hU)
  have hm : q.pr (incA D D.host.xi0) * q.pr (incA D D.host.xi0⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one, map_one]
  have h3 := congrArg (valuation k) hm
  rw [map_mul, map_one] at h3
  by_contra hne
  have hlt : valuation k (q.pr (incA D D.host.xi0)) < 1 := lt_of_le_of_ne h1 hne
  have : valuation k (q.pr (incA D D.host.xi0)) * valuation k (q.pr (incA D D.host.xi0⁻¹)) < 1 :=
    mul_lt_one_of_lt_of_le hlt h2
  rw [h3] at this
  exact lt_irrefl _ this

end GlobalTheory.SplitWeilChar

namespace GlobalTheory.SplitWeilChar

theorem weil_char_conductor_one : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → q.UnitAA → ∃ ψk : AddChar k Circle, (ofSplit q).IsChar ψ ψk ∧ HasConductor ψk 1 := by
  intro D k _ _ _ _ q ψ hψ hU
  obtain ⟨⟨ψk, hk⟩, -⟩ := GlobalTheory.LocChar.weil_char_split D k (ofSplit q) ψ hψ
  set u : k := q.pr (incA D D.host.xi0) with hu
  have hv : valuation k u = 1 := valuation_pr_incA_xi0_eq_one_of_unitAA q hU
  have hu0 : u ≠ 0 := fun h => by rw [h, map_zero] at hv; exact zero_ne_one hv
  let χ : AddChar k Circle := ψk.mulShift u⁻¹
  have hχ : q.IsChar ψ χ := by
    intro a
    have e1 : (χ a : ℂ) = psiE ψ (incA D D.host.xi0 * q.sec (u⁻¹ * a)) := hk (u⁻¹ * a)
    have e2 := GlobalTheory.SplitCharCond.sec_mul_pr q (u⁻¹ * a) (incA D D.host.xi0)
    rw [← hu, show u⁻¹ * a * u = a by field_simp] at e2
    rw [e1, ← e2]
  have hc1 : HasConductor χ 1 := GlobalTheory.SplitCharCond.hasConductor_one D k q ψ χ hψ hχ hU
  have hcu : HasConductor χ (Units.mk0 u hu0) := by
    intro x
    rw [Units.val_mk0, hv]
    have := hc1 x
    rwa [Units.val_one, map_one] at this
  have he : ψk = χ.mulShift ((Units.mk0 u hu0 : kˣ) : k) := by
    ext x
    simp only [χ, AddChar.mulShift_apply, Units.val_mk0]
    rw [← mul_assoc, inv_mul_cancel₀ hu0, one_mul]
  refine ⟨ψk, hk, ?_⟩
  rw [he]
  exact GlobalTheory.CollapseCompare.hasConductor_mulShift hcu

end GlobalTheory.SplitWeilChar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitPointWeilCharConductorOneOfUnitsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitPoint_weilChar_conductor_one_of_units : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → q.UnitAA → ∃ ψk : AddChar k Circle, (ofSplit q).IsChar ψ ψk ∧ HasConductor ψk 1 := by
  first | exact @GlobalTheory.SplitWeilChar.weil_char_conductor_one | exact GlobalTheory.SplitWeilChar.weil_char_conductor_one | (intros; apply GlobalTheory.SplitWeilChar.weil_char_conductor_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinPartIdemSumMulInvMem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IdemSumInt

theorem finPart_idemSum_mul_inv_mem : ∀ (D : D7) (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ t : 𝓞 D.host.E, (∀ Q ∈ SS, t ∉ Q.asIdeal) → finPart D (e * incA D ((t : D.host.E))⁻¹) ∈ intAE D := by
  intro D e SS hS t ht
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := hS
  by_cases h0 : t = 0
  · subst h0
    simp
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [Finset.sum_mul, map_sum]
      refine AddSubgroup.sum_mem _ fun PP hPP => ?_
      by_contra hn
      exact ht PP hPP (((hes PP hPP).2 t h0).2 hn)

end GlobalTheory.IdemSumInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceIdempotentMulIdemSumEqZeroOfNotMem
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceIdempotentMulIdemSumEqZeroOfNotMem
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.OutsideOrth

theorem mul_eq_zero : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (PP : Formalism.L2.DIV.Pl D.host.E) (e : AE D),
    PP ∉ P → Formalism.L2.NTheta.IsIdemAt p.e PP → IsIdemSum e P → e * p.e = 0 := by
  intro D k _ _ _ _ p P PP e hPP hp he
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  rw [Finset.sum_mul]
  refine Finset.sum_eq_zero fun P' hP' => ?_
  rw [mul_comm]
  exact Formalism.IndefR.Fin.idem_orth (Formalism.IndefR.Fin.idemAt_split hp) hp (hes P' hP')
    (fun h => hPP (h ▸ hP'))

end GlobalTheory.LocMod.OutsideOrth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceIdempotentMulIdemSumEqZeroOfNotMemStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceIdempotent_mul_idemSum_eq_zero_of_not_mem : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (PP : Formalism.L2.DIV.Pl D.host.E) (e : AE D), PP ∉ P → Formalism.L2.NTheta.IsIdemAt p.e PP → IsIdemSum e P → e * p.e = 0 := by
  first | exact @GlobalTheory.LocMod.OutsideOrth.mul_eq_zero | exact GlobalTheory.LocMod.OutsideOrth.mul_eq_zero | (intros; apply GlobalTheory.LocMod.OutsideOrth.mul_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RdAt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section

namespace GlobalTheory.MovedDat

def RdAt {D : D7} {c : Comm D} {v : VCom c} (G : GLoc v) (PP : Formalism.L2.DIV.Pl D.host.E) (x : G.S.P.J)
    (g : GL (Fin D.R.r) (Formalism.L2.DIV.kP PP)) : Prop :=
  ∀ (a b : Fin D.R.k ⊕ Fin (G.s + 1)) (a' b' : Fin D.R.r), a'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a →
    b'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ b → ∀ z : 𝓞 D.host.E, Ideal.Quotient.mk PP.asIdeal z = g.val a' b' →
      valuation G.k ((x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val a b - (ofSplit G.q).pr (z : D.host.E)) < 1

end GlobalTheory.MovedDat

end
end
