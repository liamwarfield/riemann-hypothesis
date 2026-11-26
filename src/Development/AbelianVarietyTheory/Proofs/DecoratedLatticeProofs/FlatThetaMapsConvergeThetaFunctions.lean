module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapIntertwinesCoreHeisenbergOperators
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapIntegrableAndBoundedLinearForm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSiegelWeilSectionMemDegeneratePrincipalS
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeOfMemPartW
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegrableContAut
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalFinitePartMemHomLatticeCompletionIff
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualStabilizerWithPrescribedSplitPlace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilVacuumFiniteSelfDualLatticeSplitting
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentRowsMap

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctions
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapIntegrableAndBoundedLinearFormStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatMap_integrable_and_bounded_linearForm : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (vS : VolM D W.rank ρ) (vT : VolM D σ V₀.rank) (vU : VolU D ρ) (x : Matrix (Fin W.rank) (Fin ρ) D.host.E), LinearIndependent D.host.E x.transpose → ∀ y : Mx D V₀.rank σ, (∀ Ψ, IsThetaFunO ψ V W Ψ → ∀ w, Integrable (flatFun ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 (rat x) y Ψ w) vU.ν) ∧ ∀ w, IsSobForm ψ θ V W fun Ψ => flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 vU.ν (rat x) y Ψ w := by
  first | exact @GlobalTheory.Unf.FlatForm.flatAt_isSobForm | exact GlobalTheory.Unf.FlatForm.flatAt_isSobForm | (intros; apply GlobalTheory.Unf.FlatForm.flatAt_isSobForm <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapIntertwinesCoreHeisenbergOperatorsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatMap_intertwines_core_heisenbergOperators : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (vS : VolM D W.rank ρ) (vT : VolM D σ V₀.rank) (vU : VolU D ρ) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (Ψ : WO V W → ℂ), IsThetaFunO ψ V W Ψ → (∀ w, evalAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 (heisO ψ V W (dV.ext0 W (dW.inc0 V₀ w)) Ψ) x y = heisO ψ V₀ W₀ w (evalAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 Ψ x y)) ∧ (∀ w, flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 vU.ν x y (heisO ψ V W (dV.ext0 W (dW.inc0 V₀ w)) Ψ) = heisO ψ V₀ W₀ w (flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 vU.ν x y Ψ)) ∧ ∀ γ, flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 vU.ν x y Ψ (ratW W₀ V₀ γ) = flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 vU.ν x y Ψ 0 := by
  first | exact @GlobalTheory.FlatHeis.flatAt_heisO | exact GlobalTheory.FlatHeis.flatAt_heisO | (intros; apply GlobalTheory.FlatHeis.flatAt_heisO <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctions
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf.Flat

variable {D : D7}

def coreMap {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) : WO V₀ W₀ →+ WO V W :=
  (dV.ext0 W).comp (dW.inc0 V₀)

theorem coreMap_eq {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) :
    ⇑(coreMap dV dW) = fun w => (dW.j0 * w) * dV.p0 := by
  funext w; rfl

theorem continuous_coreMap {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) :
    Continuous (coreMap dV dW) := by
  rw [coreMap_eq]
  exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem coreMap_finPart {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (w : WO V₀ W₀)
    (h : w.map (finPart D) = 0) : (coreMap dV dW w).map (finPart D) = 0 := by
  show ((dW.j0 * w) * dV.p0).map (finPart D) = 0
  rw [Matrix.map_mul, Matrix.map_mul, h, Matrix.mul_zero, Matrix.zero_mul]

theorem coreMap_infPart {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (w : WO V₀ W₀)
    (h : w.map (infPart D) = 0) : (coreMap dV dW w).map (infPart D) = 0 := by
  show ((dW.j0 * w) * dV.p0).map (infPart D) = 0
  rw [Matrix.map_mul, Matrix.map_mul, h, Matrix.mul_zero, Matrix.zero_mul]

theorem flatLaw : ∀ D : D7, FlatLaw D := by
  intro D ψ hψ V V₀ W W₀ ρ σ dV dW vS vT vU x hx y Ψ hΨ
  obtain ⟨θ, hθ⟩ := GlobalTheory.AdelicU.exists_isInfFam D
  have hF := GlobalTheory.T.flatMap_integrable_and_bounded_linearForm D ψ hψ θ hθ V V₀ W W₀ ρ σ dV dW vS vT vU x hx y
  refine ⟨hF.1 Ψ hΨ, ?_⟩
  exact GlobalTheory.T.theta_of_heisenberg_intertwiner_bounded_at_zero D ψ hψ θ hθ V W V₀ W₀ (coreMap dV dW) (continuous_coreMap dV dW)
    (coreMap_finPart dV dW) (coreMap_infPart dV dW)
    (fun f => flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 vU.ν (rat x) y f) (hF.2 0)
    (fun f w hf => ((GlobalTheory.T.flatMap_intertwines_core_heisenbergOperators D ψ hψ V V₀ W W₀ ρ σ dV dW vS vT vU (rat x) y f hf).2.1 w))
    (fun f γ hf => ((GlobalTheory.T.flatMap_intertwines_core_heisenbergOperators D ψ hψ V V₀ W W₀ ρ σ dV dW vS vT vU (rat x) y f hf).2.2 γ)) Ψ hΨ

end GlobalTheory.Unf.Flat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctionsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatThetaMaps_converge_thetaFunctions : ∀ D : D7, FlatLaw D := by
  first | exact @GlobalTheory.Unf.Flat.flatLaw | exact GlobalTheory.Unf.Flat.flatLaw | (intros; apply GlobalTheory.Unf.Flat.flatLaw <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaMajorantAverageIdentity
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section

namespace GlobalTheory.IkedaK

variable {D : D7}

theorem bdd_om_compact {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : WRep S T}
    (hW : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {P : Set (GA D S × GA D T)}
    (hP : IsCompact P) : ∃ C : ℝ, ∀ p ∈ P, ∀ x, ‖om p f x‖ ≤ C := by
  obtain ⟨-, -, -, -, -, K, hK, hKc⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank S.rank
  have hc := GlobalTheory.Unf.jointCont_all D ψ S T χS χT om hW f hf
  obtain ⟨C, hC⟩ := (hP.prod hK).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, fun p hp x => ?_⟩
  obtain ⟨γ, ⟨γ', rfl⟩, hx⟩ := hKc x
  have hq := (hW.om_pres p f hf).quasi γ' x
  have e : (((incA D).toAddMonoidHom.mapMatrix (m := Fin T.rank) (n := Fin S.rank)) γ') = ratW T S γ' := rfl
  rw [e] at hx
  have h1 := hW.std.1.2.1 (-(symplOH S T (ratW T S γ') x))
  have := hC (p, ratW T S γ' + x) ⟨hp, hx⟩
  simp only at this
  rw [hq, norm_mul, h1, one_mul] at this
  exact this

theorem om_mul_apply {S T : HSp D} (om : WRep S T) (p q : GA D S × GA D T) (f : WO S T → ℂ) :
    om p (om q f) = om (p * q) f := by
  rw [map_mul]; rfl

theorem weilRepUnitaryPair_left_apply_right {S T : HSp D} (om : WRep S T) (g : GA D S) (k : GA D T) (f : WO S T → ℂ) :
    om (g, 1) (om (1, k) f) = om (g, k) f := by
  rw [om_mul_apply]; congr 1; ext <;> simp

theorem weilRepUnitaryPair_right_apply_left {S T : HSp D} (om : WRep S T) (g : GA D S) (k : GA D T) (f : WO S T → ℂ) :
    om (1, k) (om (g, 1) f) = om (g, k) f := by
  rw [om_mul_apply]; congr 1; ext <;> simp

end GlobalTheory.IkedaK
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsNormalFr
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam

variable {D : D7}

abbrev FYFam {a : XGeo D} {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E} (l : LocX a βT PP) : Type :=
  ∀ j c, j + c = l.s + 1 → Frame l.k (Yc D j).rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c)

def IsNormalFr {a : XGeo D} {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E} (l : LocX a βT PP) (y : YRat a)
    (FY : FYFam l) (sc : ℕ → l.k) : Prop :=
  (∀ j, valuation l.k (sc j) = 1) ∧ (∀ j, sc (j + 1 + 1) = sc j * (ofSplit l.q).xi) ∧
  (∀ j ρ h, valuation l.k ((ofSplit l.q).hz ((y.bes j ρ h).lev (a.x j).vol)) = 1) ∧
  (∀ j ρ h c (hc : j + c = l.s + 1), (ofSplit l.q).IsBesFrame ((y.bes j ρ h).lev (a.x j).vol) (sc j) (l.FX j (by omega))
    (FY j c hc)) ∧
  (∀ j ρ h c (hc : j + 1 + c = l.s + 1), (ofSplit l.q).IsJacFrame ((y.jac j ρ h).lev (a.x (j + 1)).vol) (sc j)
    ((ofSplit l.q).hz ((y.bes j ρ h).lev (a.x j).vol)) (l.FX (j + 1) (by omega)) (FY (j + 1) c hc)) ∧
  ∀ h, (y.τ l.s h).map (ofSplit l.q).pr *ᵥ (fun i => (ofSplit l.q).pr (a.ζ₀ i)) =
    (-((ofSplit l.q).xi * sc l.s)) • fun i => (ofSplit l.q).pr ((y.bes l.s 0 h).ζ i)

end GlobalTheory.Fam

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedThetaCorrespondenceAllGoodPrimes
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedThetaCorrespondenceAllGoodPrimes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

namespace GlobalTheory.UnrAll

theorem unrCorr_all : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, UnrCorr R i t (fun _ => True) := by
  intro _hDec hHowe D G _ _ Pl0 T A Ks _ _ _ R F hG hFull i t h hh s c y hy h1 h2 B B' hB hB' w hw _
  by_cases hc : Formalism.IndefR.Lev.IsConjPl w w
  · exact GlobalTheory.DownInert.unrCorr_inert hHowe D G Pl0 T A Ks R F hG hFull i t h hh s c y hy h1 h2 B B' hB hB' w hw hc
  · exact GlobalTheory.SplitCorr.unrCorr_split D G Pl0 T A Ks R F hG hFull i t h hh s c y hy h1 h2 B B' hB hB' w hw hc

end GlobalTheory.UnrAll
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedThetaCorrespondenceAllGoodPrimesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedThetaCorrespondence_all_goodPrimes : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, UnrCorr R i t (fun _ => True) := by
  first | exact @GlobalTheory.UnrAll.unrCorr_all | exact GlobalTheory.UnrAll.unrCorr_all | (intros; apply GlobalTheory.UnrAll.unrCorr_all <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RootOfUnityThetaTwist
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NormEmbeddingHostFormConstantEq
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.ExtCore

theorem isDetRoot_mul {D : D7} (V : HSp D) (g g' : GA D V) (x x' : (AE D)ˣ) (hx : IsDetRoot V g x)
    (hx' : IsDetRoot V g' x') : IsDetRoot V (g * g') (x * x') := by
  unfold IsDetRoot at *
  rw [Units.val_mul, (matHom V).map_mul, Units.val_mul, Matrix.det_mul, RingHom.map_mul]
  conv_lhs => rw [hx, hx']
  ring


end GlobalTheory.ExtCore
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.TupRoot

variable {D : D7}

theorem finite_pow_eq_one (n : ℕ) (hn : 0 < n) : {z : Circle | z ^ n = 1}.Finite := by
  refine ((Polynomial.nthRoots n (1 : ℂ)).toFinset.finite_toSet.preimage
    (Set.injOn_of_injective Circle.coe_injective)).subset fun z hz => ?_
  simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots hn]
  have hz' : z ^ n = 1 := hz
  have := congrArg (fun w : Circle => (w : ℂ)) hz'
  simpa using this

theorem isOpen_ker_of_pow {X : Type} [TopologicalSpace X] [Group X] (c : X →* Circle) (hc : Continuous c) (n : ℕ) (hn : 0 < n)
    (hp : ∀ x, c x ^ n = 1) : IsOpen (c.ker : Set X) := by
  have hF : ({z : Circle | z ^ n = 1} \ {1}).Finite := (finite_pow_eq_one n hn).diff
  have ho := hF.isClosed.isOpen_compl.preimage hc
  convert ho using 1
  ext x
  simp [hp x]

theorem pow_eq_one_of_chrEq {c : (AE D)ˣ →* Circle} {χ : Formalism.L2.Host.HChar D.host.E} (h : ChrEq c χ) {n : ℕ}
    (hn : χ.OrderDvd n) (x : (AE D)ˣ) : c x ^ n = 1 := by
  have := GlobalTheory.HeckeFinTrivial.eq_one_of_trivial_on_finite D ((powMonoidHom n).comp c)
    ⟨(continuous_pow n).comp h.1.1, fun k => by
      have := h.1.2 k
      simp only [MonoidHom.coe_comp, Function.comp_apply, powMonoidHom_apply]
      erw [this, one_pow]⟩
    (fun y hy => by simpa using GlobalTheory.T.idelicCharacter_pow_eq_one_finiteIdeles_of_orderDvd D c χ h n hn y hy) x
  simpa using this

theorem eq_one_of_finPart {c : (AE D)ˣ →* Circle} {χ : Formalism.L2.Host.HChar D.host.E} (h : ChrEq c χ) {n : ℕ} (hn0 : 0 < n)
    (hn : χ.OrderDvd n) (x : (AE D)ˣ) (hx : finPart D (x : AE D) = 1) : c x = 1 :=
  GlobalTheory.UnivCover.OpenKerChar.map_eq_one_of_finPart_eq_one D c
    (isOpen_ker_of_pow c h.1.1 n hn0 (pow_eq_one_of_chrEq h hn)) x hx

theorem twist_eq {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χS χT ν : (AE D)ˣ →* Circle}
    {om om' : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om)
    (hW' : IsWeilDatumO ψ S T (χS * ν) (χT * ν) om') {g : GA D S} {h : GA D T} {x y : (AE D)ˣ}
    (hx : IsDetRoot S g x) (hy : IsDetRoot T h y) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    om' (g, h) f = (((ν x)⁻¹ * ν y : Circle) : ℂ) • om (g, h) f := by
  rw [GlobalTheory.T.weilData_differ_by_splittingFactorQuotient D ψ S T χS χT _ _ om om' hW hW' g h x y hx hy f hf]
  congr 1
  have e : splitFacO (χS * ν) (χT * ν) x y = (ν x)⁻¹ * ν y * splitFacO χS χT x y := by
    simp only [splitFacO, MonoidHom.mul_apply]
    rw [mul_inv]
    ac_rfl
  rw [e, Circle.coe_mul, mul_assoc, mul_inv_cancel₀ (Circle.coe_ne_zero _), mul_one]

theorem isWeil_rec {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle} {n n' : ℕ} (e : n = n')
    (om : Om (Yc D n) D.sp.X') (h : IsWeilDatumO ψ (Yc D n) D.sp.X' χS χT om) :
    IsWeilDatumO ψ (Yc D n') D.sp.X' χS χT (Eq.rec (motive := fun n _ => Om (Yc D n) D.sp.X') om e) := by
  subst e
  exact h

end GlobalTheory.TupRoot
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilFockDoubledPairOfWeilAndIchino
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilFockDoubledPairOfWeilAndIchino
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem lagr_eq_lagr {D : D7} (A B : HSp D) (y : WO A B) :
    GlobalTheory.SiegelFormula.lagr A B y = GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.lagr A B y := by
  ext i j
  obtain ⟨k | k, rfl⟩ := finSumFinEquiv.surjective j
  · simp only [GlobalTheory.SiegelFormula.lagr, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.lagr, Matrix.of_apply, pairVec_inl, Equiv.symm_apply_apply,
      Sum.elim_inl]
  · simp only [GlobalTheory.SiegelFormula.lagr, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.lagr, Matrix.of_apply, pairVec_inr, Equiv.symm_apply_apply,
      Sum.elim_inr, Pi.neg_apply]

theorem swSection_eq_swSec {D : D7} (A B : HSp D) (ν : Measure (WO A B)) (𝓕 : Set (WO A B))
    (ω : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)) (f : WO (dblSp A) B → ℂ) :
    GlobalTheory.SiegelFormula.swSection A B ν 𝓕 ω f = swSec A B ω ν 𝓕 f := by
  funext g
  simp only [GlobalTheory.SiegelFormula.swSection, GlobalTheory.SiegelFormula.valZero, swSec, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.evZero, lagr_eq_lagr]

theorem isHeckeCharacter_inv_of_isHeckeCharacter {D : D7} {χ : (AE D)ˣ →* Circle} (h : IsHeckeChar D χ) : IsHeckeChar D χ⁻¹ := by
  refine ⟨?_, fun x => ?_⟩
  · have : (χ⁻¹ : (AE D)ˣ →* Circle) = fun x => (χ x)⁻¹ := rfl
    rw [this]; exact h.1.inv
  · rw [MonoidHom.inv_apply, h.2 x, inv_one]

end GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem siegelWeilAll_of_hypotheses : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary →
    GlobalTheory.Published.SiegelWeilUnitaryConvergent → ∀ D : D7, SiegelWeilFock D := by
  intro hW hWeil hIch D ψ A B ha hab hwitt χB omh homh a hmaj θ sS sB hθ hS hB hKc ν 𝓕 hcov mH hmH φ hF
  have hφ := hF.1
  have hK := GlobalTheory.T.fock_vector_finite_under_compact_commuting_cartan D ψ θ (dblSp A) B 1 χB omh sS sB homh hθ hS hB (Khat A a) (isCompact_Khat A a) hKc φ hF
  have hI : HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a) :=
    GlobalTheory.T.adelicIwasawa_doubledGroup_selfDualLattice D A (frameLat A) a (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat A) hmaj
  have hwitt' : Formalism.MainNotions.SchurIrreducible.wittIdx B = 0 ∨ A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank := by
    rw [GlobalTheory.RallisIP.wittIdx_eq_wittIndex]; exact hwitt
  by_cases hb : B.rank ≤ 2 * A.rank
  · have h3 : A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank := by
      rcases hwitt' with h | h
      · rw [h]; omega
      · exact h
    exact hIch D ψ A B hab hb h3 χB omh homh a hmaj hI θ sS sB hθ hS hB hKc ν 𝓕 hcov mH hmH φ hF
  · push_neg at hb
    obtain ⟨-, hW2⟩ := hWeil D A B mH hmH ha hwitt'
    obtain ⟨hint, hser⟩ := hW2 ψ χB omh homh φ hφ
    refine ⟨hint, ?_⟩
    obtain ⟨-, -, hsum⟩ : _ ∧ _ ∧ _ := by
      obtain ⟨h1, h2⟩ := hser hb ν 𝓕 hcov
      exact ⟨h1, fun g => (h2 g).1, fun g => (h2 g).2⟩
    have hmem := GlobalTheory.T.doublingSiegelWeilSection_mem_degeneratePrincipalSeries hW D ψ A B χB omh homh ν 𝓕 hcov φ hφ a hK
    have hre : (A.rank : ℝ) / 2 < (sZero A B).re := by
      have : (sZero A B).re = ((B.rank : ℝ) - A.rank) / 2 := by
        simp [sZero, Complex.div_re]
      rw [this]
      have : (2 * A.rank : ℝ) < B.rank := by exact_mod_cast hb
      linarith
    have hv := GlobalTheory.Eis.SphConv.eisValueAt_flat hI hmem (GlobalTheory.Eis.sphConv D A a hI) (isHeckeCharacter_inv_of_isHeckeCharacter homh.hecT) hre
    have he : GlobalTheory.Eis.eis A (swSec A B omh ν 𝓕 φ) = ThetaMean.thetaMean omh mH φ := by
      funext g
      rw [← swSection_eq_swSec]
      exact hsum g
    rw [he] at hv
    exact hv

end GlobalTheory.Core.Rk.IP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilFockDoubledPairOfWeilAndIchinoStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelWeil_fockDoubledPair_of_weil_and_ichino : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → ∀ D : D7, SiegelWeilFock D := by
  first | exact @GlobalTheory.Core.Rk.IP.siegelWeilAll_of_hypotheses | exact GlobalTheory.Core.Rk.IP.siegelWeilAll_of_hypotheses | (intros; apply GlobalTheory.Core.Rk.IP.siegelWeilAll_of_hypotheses <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StdCharSymplecticHalfPeriodLatticeEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StdCharSymplecticHalfPeriodLatticeEqOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.HalfPairing
open GlobalTheory.LatVac

variable {D : D7} {S T : HSp D} {N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem toMatrix_mem_latRat (hc : D.host.ccK = ⊤) (hN : IsSelfDualC S N) {x : Formalism.L2.Col.HomE D.host.E S.rank T.rank}
    (hx : x ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') :
    LinearMap.toMatrix' x ∈ latRat S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) := by
  have hA : D.host.AA = D.host.AA0 := by
    rw [Formalism.BasicNotions.Host.AA, Formalism.BasicNotions.Host.ccE, hc, Ideal.map_top, FractionalIdeal.coeIdeal_top, one_mul]
  obtain ⟨n, s, s', hs, hss⟩ := GlobalTheory.LatVacDual.dualFamily D S N hN
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨r, hr, x, hx, rfl⟩ := hz
    have e : LinearMap.toMatrix' (r • x) = ∑ k, genMap S T r (s' k) (x (s k)) := by
      refine Matrix.ext fun i j => ?_
      have h1 : (Pi.single j 1 : Fin S.rank → D.host.E) = ∑ k, (∑ l, star (s' k l) * S.gram l j) • s k := by
        funext a
        rw [Finset.sum_apply, Pi.single_apply, ← hss a j]
        exact Finset.sum_congr rfl fun k _ => mul_comm _ _
      rw [Matrix.sum_apply, LinearMap.toMatrix'_apply]
      change r * x (Pi.single j 1) i = _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [h1, map_sum, Finset.sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, Pi.smul_apply, smul_eq_mul, genMap, Matrix.of_apply]
      ring
    rw [e]
    exact sum_mem fun k _ => AddSubgroup.subset_closure ⟨r, hA ▸ hr, _, (hs k).2, _, hx _ (hs k).1, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx =>
    have e : LinearMap.toMatrix' (c • x) = (c : D.host.E) • LinearMap.toMatrix' x := by
      ext i j; rfl
    rw [e]
    exact smul_mem_latRat c hx

theorem smul_mem_locP {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ} {SS : Finset (HeightOneSpectrum (𝓞 E))}
    {M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)} {c : ℕ} (hc : 0 < c) {y : Formalism.L2.Col.HomE E a b} (hy : y ∈ halfBO SS M c)
    (Q : HeightOneSpectrum (𝓞 E)) : (c : E) • y ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := by
  have h : ((c : E) ^ expS SS Q)⁻¹ • y ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := (Submodule.mem_iInf _).1 hy Q
  have hc' : (c : E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  have key : ∀ k : ℕ, (c : E) = (c : E) ^ k * ((c : E) ^ expS SS Q)⁻¹ → (c : E) • y ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := fun k hk => by
    have := nsmul_mem h (c ^ k)
    rwa [← Nat.cast_smul_eq_nsmul E, smul_smul, Nat.cast_pow, ← hk] at this
  unfold expS at key
  split_ifs at key
  · exact key 2 (by field_simp)
  · exact key 0 (by simp)
  · exact key 1 (by simp)

theorem conj_comp_mem (hc : D.host.ccK = ⊤) (hN : IsSelfDualC S N) {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)}
    (he : Formalism.L2.NTheta.IsIdemAt e P) (h0 : infPart D e = 0) {x : Formalism.L2.Col.HomE D.host.E S.rank T.rank}
    (hx : x ∈ Formalism.HermitianLatticesTheory.localization₂ (Formalism.L2.Col.conjPrime₂ P).asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N')) :
    ((LinearMap.toMatrix' x).map fun r => cA D e * incA D r : WO S T) ∈
      latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True := by
  obtain ⟨s, hs, hsx⟩ := hx
  have hs' : Formalism.L2.Col.cO D.host.E s ∉ P.asIdeal := hs
  have hne : Formalism.L2.Col.cO D.host.E s ≠ 0 := fun h => hs' (h ▸ zero_mem _)
  have hs0 : (s : D.host.E) ≠ 0 := fun h => hne (by rw [show s = 0 from RingOfIntegers.ext h, map_zero])
  have h1 : finPart D (e * incA D ((Formalism.L2.Col.cO D.host.E s : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra h
    exact hs' ((he.2 _ hne).2 h)
  have h2 := GlobalTheory.PlaceVec.cF_mem_int (GlobalTheory.IdemIntegral.toEAf_mem_of_finPart h1)
  rw [← GlobalTheory.AdelicLatMove.toEAf_cA, RingHom.map_mul (cA D)] at h2
  have h3 : cA D (incA D ((Formalism.L2.Col.cO D.host.E s : D.host.E)⁻¹)) = incA D (s : D.host.E)⁻¹ := by
    change incA D (star (star (s : D.host.E))⁻¹) = _
    rw [star_inv₀, star_star]
  rw [h3] at h2
  have h4 := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ (GlobalTheory.PlaceVec.finPart_mem_intAE h2) _
    (finTens_mem_latO (one_mem_intAf _) (toMatrix_mem_latRat hc hN hsx))
  convert h4 using 1
  ext i j
  have h5 := GlobalTheory.PlaceVec.infPart_cA h0
  rw [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  refine GlobalTheory.SplitScalar.adele_ext (by simp only [RingHom.map_mul, h5, zero_mul]) ?_
  have h6 : finPart D (finTens 1 (LinearMap.toMatrix' (s • x)) i j) =
      finPart D (incA D ((s : D.host.E) * LinearMap.toMatrix' x i j)) := rfl
  rw [RingHom.map_mul (finPart D) (_ * _), h6, ← RingHom.map_mul, mul_assoc, ← RingHom.map_mul (incA D),
    inv_mul_cancel_left₀ hs0]

theorem char_sympl_halfB : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (c : ℕ), 0 < c → Odd c → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → LaFacts (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' → (∃ ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E), IsSelfDualC S ΛS ∧ (ΛS : Set (Fin S.rank → D.host.E)) = latFr S hS N) → (∃ ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E), IsSelfDualC T ΛT ∧ (ΛT : Set (Fin T.rank → D.host.E)) = latFr T hT N') → ∀ y' ∈ halfBO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, ∀ u ∈ (latO S T (latFr S hS N) (latFr T hT N') fun _ => True), ψ (symplO S T (c • u) (((LinearMap.toMatrix' (y')).reindex (finCongr hT.symm) (finCongr hS.symm)).map fun r => cA D e * incA D r)) = 1 := by
  intro D ψ θ S T a b hS hT δ sc hP e SS hE N N' c hc _ _ _ ⟨ΛS, dS, eS⟩ ⟨ΛT, dT, eT⟩ y hy u hu
  subst hS hT
  obtain rfl : ΛS = N := SetLike.coe_injective eS
  obtain rfl : ΛT = N' := SetLike.coe_injective eT
  rw [← eS, ← eT] at hu
  change ψ (symplO S T (c • u) ((LinearMap.toMatrix' y).map fun r => cA D e * incA D r)) = 1
  have hmem : c • ((LinearMap.toMatrix' y).map fun r => cA D e * incA D r : WO S T) ∈
      latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True := by
    obtain ⟨⟨es, hes, rfl⟩, -⟩ := hE
    have e1 : c • ((LinearMap.toMatrix' y).map fun r => cA D (∑ PP ∈ SS, es PP) * incA D r : WO S T) =
        ∑ PP ∈ SS, ((LinearMap.toMatrix' ((c : D.host.E) • y)).map fun r => cA D (es PP) * incA D r : WO S T) := by
      ext i j
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Matrix.smul_apply, Matrix.map_apply, Matrix.sum_apply, map_sum, nsmul_eq_mul, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun PP _ => ?_
      change _ = cA D (es PP) * incA D ((c : D.host.E) * LinearMap.toMatrix' y i j)
      rw [RingHom.map_mul (incA D), map_natCast, mul_left_comm]
    rw [e1]
    refine sum_mem fun PP hPP => conj_comp_mem hP.cc dS (hes PP hPP) ?_ (smul_mem_locP hc hy _)
    refine GlobalTheory.PlaceVec.idemSum_infPart (P := {PP}) ⟨⟨es, fun Q hQ => ?_, (Finset.sum_singleton _ _).symm⟩, (hes PP hPP).1.2.1⟩
    rw [Finset.mem_singleton.1 hQ]
    exact hes PP hPP
  have h := char_sympl_eq_one hP.std dS dT hu hmem
  rw [← symplHom_apply, map_nsmul] at h
  rw [← symplHom_apply, map_nsmul]
  exact h

end GlobalTheory.AdForm.HalfPairing
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StdCharSymplecticHalfPeriodLatticeEqOneStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stdChar_symplectic_halfPeriodLattice_eq_one : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (c : ℕ), 0 < c → Odd c → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → LaFacts (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' → (∃ ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E), IsSelfDualC S ΛS ∧ (ΛS : Set (Fin S.rank → D.host.E)) = latFr S hS N) → (∃ ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E), IsSelfDualC T ΛT ∧ (ΛT : Set (Fin T.rank → D.host.E)) = latFr T hT N') → ∀ y' ∈ halfBO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, ∀ u ∈ (latO S T (latFr S hS N) (latFr T hT N') fun _ => True), ψ (symplO S T (c • u) (((LinearMap.toMatrix' (y')).reindex (finCongr hT.symm) (finCongr hS.symm)).map fun r => cA D e * incA D r)) = 1 := by
  first | exact @GlobalTheory.AdForm.HalfPairing.char_sympl_halfB | exact GlobalTheory.AdForm.HalfPairing.char_sympl_halfB | (intros; apply GlobalTheory.AdForm.HalfPairing.char_sympl_halfB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftWittIndexVanishing
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

end GlobalTheory.Core.Rk.IP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdemAtUniqueOrth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod GlobalTheory.Mem GlobalTheory.Mem.Col2 Formalism.L2.Col Formalism.L2.Forms
open scoped Classical

namespace GlobalTheory.PlaceIdemUniq

theorem idemAt_unique_orth : ∀ (D : D7) (a b : AE D) (PP PP' : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt a PP → Formalism.L2.NTheta.IsIdemAt b PP' → (PP = PP' → a = b) ∧ (PP ≠ PP' → a * b = 0) := by
  intro D a b PP PP' ha hb
  refine ⟨fun h => ?_, fun h => ?_⟩
  · subst h
    exact Formalism.IndefR.Fin.idemAt_eq_split (Formalism.IndefR.Fin.idemAt_split ha) ha hb
  · exact Formalism.IndefR.Fin.idem_orth (Formalism.IndefR.Fin.idemAt_split ha) ha hb h

end GlobalTheory.PlaceIdemUniq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSymmetricDataConductorOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LocMod.SymChainAt
open GlobalTheory.FinPl (SplitPt idAt intAt)
open Formalism.L2.NTheta (IsIdemAt)
open _root_.Formalism.L2.Col (IntAt)

section Place
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k)

theorem sec_one : q.sec 1 = q.e := by
  have := q.sec_pr 1
  rwa [map_one, mul_one] at this

theorem pr_e : q.pr q.e = 1 := by rw [← sec_one, q.pr_sec]

theorem pr_e_mul (x : AE D) : q.pr (q.e * x) = q.pr x := by rw [map_mul, pr_e, one_mul]

theorem place_facts {PP : Formalism.L2.DIV.Pl D.host.E} (h : IsIdemAt q.e PP) :
    (∀ a, (ofSplit q).pr a ∈ 𝒪[k] ↔ IntAt PP a) ∧ DenseRange (ofSplit q).pr := by
  obtain ⟨k₀, _, _, _, _, q₀, he, -, hi, hd⟩ := GlobalTheory.LocMod.SplitCompl.exists_place D PP q.e h
  refine ⟨fun a => ?_, ?_⟩
  · rw [← hi, q.int_iff, q₀.int_iff]
    change finPart D (q.sec (q.pr _)) ∈ _ ↔ finPart D (q₀.sec (q₀.pr _)) ∈ _
    rw [q.sec_pr, q₀.sec_pr, he]
  · have hs : Function.Surjective (fun x => q.pr (q₀.sec x)) := fun y =>
      ⟨q₀.pr (q.sec y), by simp only [q₀.sec_pr, he, pr_e_mul, q.pr_sec]⟩
    have := hs.denseRange.comp hd (q.cont_pr.comp q₀.cont_sec)
    convert this using 1
    funext a
    change q.pr _ = q.pr (q₀.sec (q₀.pr _))
    rw [q₀.sec_pr, he, pr_e_mul]

def prO : 𝓞 D.host.E →+* k := (q.pr.comp (incA D)).comp (algebraMap (𝓞 D.host.E) D.host.E)

theorem sec_mul (x y : k) : q.sec x * q.sec y = q.sec (x * y) := by
  have h := q.sec_pr (q.sec x * q.sec y)
  rw [map_mul, q.pr_sec, q.pr_sec, ← mul_assoc, ← GlobalTheory.FrameGlob.sec_eq_mul] at h
  exact h.symm

theorem idl_mul (x y : k) (h : x * y = 1) : (q.sec x + (1 - q.e)) * (q.sec y + (1 - q.e)) = 1 := by
  have h1 := sec_mul q x y
  rw [h, sec_one] at h1
  have h2 := GlobalTheory.FrameGlob.sec_eq_mul q x
  have h3 := GlobalTheory.FrameGlob.sec_eq_mul q y
  have h4 := q.split.1
  linear_combination h1 + h2 + h3 + h4

def idl (x : kˣ) : (AE D)ˣ :=
  ⟨q.sec x + (1 - q.e), q.sec (x⁻¹ : kˣ) + (1 - q.e), idl_mul q _ _ x.mul_inv, idl_mul q _ _ x.inv_mul⟩

end Place

end GlobalTheory.LocMod.SymChainAt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MoveCompactLevelInvariant
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.StabMove

variable {D : D7}

def IntG (V : HSp D) (g : GA D V) : Prop := ∀ i j, finPart D (Formalism.L2.Theta.mt V g i j) ∈ intAE D

theorem IntG.inv {V : HSp D} (hV : V.gram = 1) {g : GA D V} (h : IntG V g) : IntG V g⁻¹ := by
  have e : ((Formalism.L2.Theta.mt V g).map (cA D))ᵀ * V.gram.map (incA D) * Formalism.L2.Theta.mt V g = V.gram.map (incA D) := g.2
  rw [hV, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at e
  have e2 : Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g⁻¹ = 1 := by
    rw [← GlobalTheory.AdelicLatMove.mt_mul, mul_inv_cancel, GlobalTheory.AdelicLatMove.mt_one]
  have e3 : Formalism.L2.Theta.mt V g⁻¹ = ((Formalism.L2.Theta.mt V g).map (cA D))ᵀ := by
    rw [← Matrix.one_mul (Formalism.L2.Theta.mt V g⁻¹), ← e, Matrix.mul_assoc, e2, Matrix.mul_one]
  intro i j
  rw [e3, Matrix.transpose_apply, Matrix.map_apply, GlobalTheory.MovedIdem.finPart_cA]
  exact GlobalTheory.MovedIdem.sigR_mem_intAE (h j i)

theorem intG_of_moves {V : HSp D} {n : ℕ} (hn : V.rank = n) {k : GA D V}
    (h : GlobalTheory.AdForm.Moves V hn k (Formalism.L2.Col.stdLat D.host.E n)) : IntG V k⁻¹ := by
  subst hn
  intro i j
  have h1 := (h (Pi.single j 1)).1 (fun a _ => by
    rw [Pi.single_apply]
    split_ifs
    · exact Submodule.one_le.1 le_rfl
    · exact zero_mem _) i
  refine GlobalTheory.PlaceDatum.finPart_mem_of_toEAf ?_
  have e : (fun a => eToEAf D ((Pi.single j 1 : Fin V.rank → D.host.E) a)) = Pi.single j 1 := by
    funext a
    rw [Pi.single_apply, Pi.single_apply]
    split_ifs
    · exact map_one _
    · exact map_zero _
  rw [e, Matrix.mulVec_single_one] at h1
  exact h1

theorem mem_hatV_iff {n : ℕ} (u : Fin n → GlobalTheory.Ker.AfE D) :
    u ∈ GlobalTheory.Ker.hatV (GlobalTheory.SW.stdL D.host.E n) ↔ ∀ i, u i ∈ intAE D := by
  constructor
  · intro hu i
    induction hu using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      exact AddSubgroup.subset_closure ⟨a, ha, ⟨x i, (GlobalTheory.SW.Base.mem_stdL x).1 hx i⟩, rfl⟩
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | neg y _ hy => exact neg_mem hy
  · intro hu
    rw [← Finset.univ_sum_single u]
    refine sum_mem fun i _ => ?_
    have key : ∀ z ∈ intAE D, (Pi.single i z : Fin n → GlobalTheory.Ker.AfE D) ∈ GlobalTheory.Ker.hatV (GlobalTheory.SW.stdL D.host.E n) := by
      intro z hz
      induction hz using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨a, ha, x, rfl⟩ := hy
        refine AddSubgroup.subset_closure ⟨a, ha, Pi.single i (x : D.host.E), (GlobalTheory.SW.Base.mem_stdL _).2 fun b => ?_, ?_⟩
        · rw [Pi.single_apply]
          split_ifs
          · exact x.2
          · exact isIntegral_zero
        · funext b
          rw [Pi.single_apply, Pi.single_apply]
          split_ifs
          · rfl
          · rw [TensorProduct.tmul_zero]
      | zero => rw [Pi.single_zero]; exact zero_mem _
      | add y z _ _ hy hz => rw [Pi.single_add]; exact add_mem hy hz
      | neg y _ hy => rw [Pi.single_neg]; exact neg_mem hy
    exact key _ (hu i)

theorem isMov_of_intG {V : HSp D} {k : GA D V} (h : IntG V k) (h' : IntG V k⁻¹) :
    GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmt V k) (GlobalTheory.SW.stdL D.host.E V.rank) (GlobalTheory.SW.stdL D.host.E V.rank) := by
  have key : ∀ g, IntG V g → ∀ u ∈ GlobalTheory.Ker.hatV (GlobalTheory.SW.stdL D.host.E V.rank),
      GlobalTheory.Ker.fmt V g *ᵥ u ∈ GlobalTheory.Ker.hatV (GlobalTheory.SW.stdL D.host.E V.rank) := fun g hg u hu =>
    (mem_hatV_iff _).2 fun i => sum_mem (t := Finset.univ) fun j _ => GlobalTheory.GeoActCompare.TameConj.mul_mem_intAE (hg i j) ((mem_hatV_iff _).1 hu j)
  intro u
  refine ⟨fun hu => ⟨_, key _ h' u hu, ?_⟩, ?_⟩
  · rw [Matrix.mulVec_mulVec, GlobalTheory.Ker.fmt, GlobalTheory.Ker.fmt, ← Matrix.map_mul, ← GlobalTheory.AdelicLatMove.mt_mul, mul_inv_cancel,
      GlobalTheory.AdelicLatMove.mt_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  · rintro ⟨u₀, h0, rfl⟩
    exact key _ h u₀ h0

theorem finM_mul (V : HSp D) {n : ℕ} (hn : V.rank = n) (g h : GA D V) : finM V hn (g * h) = finM V hn g * finM V hn h := by
  subst hn
  change (Formalism.L2.Theta.mt V (g * h)).map (toEAf D) = (Formalism.L2.Theta.mt V g).map (toEAf D) * (Formalism.L2.Theta.mt V h).map (toEAf D)
  rw [GlobalTheory.AdelicLatMove.mt_mul, Matrix.map_mul]

theorem moves_of_mul {V : HSp D} {n : ℕ} (hn : V.rank = n) {g k : GA D V} (h : IntG V k) (h' : IntG V k⁻¹) {N}
    (hN : GlobalTheory.AdForm.Moves V hn (g * k) N) : GlobalTheory.AdForm.Moves V hn g N := by
  have key : ∀ a, IntG V a → ∀ u : Fin n → EF D, (∀ i, u i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) →
      ∀ i, (finM V hn a *ᵥ u) i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun a ha u hu i =>
    sum_mem (t := Finset.univ) fun j _ => mul_mem
      (GlobalTheory.IdemIntegral.toEAf_mem_of_finPart (ha ((finCongr hn).symm i) ((finCongr hn).symm j))) (hu j)
  intro x
  rw [hN x]
  constructor
  · intro hx
    have := key k h _ hx
    rwa [Matrix.mulVec_mulVec, ← finM_mul, _root_.mul_inv_rev, mul_inv_cancel_left] at this
  · intro hx
    have := key _ h' _ hx
    rwa [Matrix.mulVec_mulVec, ← finM_mul, ← _root_.mul_inv_rev] at this

theorem root_eq {V : HSp D} {χ : (AE D)ˣ →* Circle} {n : ℕ} (h : ResEta D χ n) (hn : Even n) {g : GA D V} {x x' : (AE D)ˣ}
    (hx : IsDetRoot V g x) (hx' : IsDetRoot V g x') : χ x' = χ x := by
  obtain ⟨a, rfl⟩ := (GlobalTheory.Member.isDetRoot_laws D V).2.1 g x x' hx hx'
  obtain ⟨⟨η, hη⟩, h2⟩ := h
  obtain ⟨m, rfl⟩ := hn
  rw [map_mul, h2 η hη a, pow_add, ← mul_pow, GlobalTheory.VolHeckeCompare.IsEta_mul_self hη, one_pow, mul_one]

theorem coe_stdL (n : ℕ) : (GlobalTheory.SW.stdL D.host.E n : Set (Fin n → D.host.E)) = intVec D n :=
  Set.ext fun x => GlobalTheory.SW.Base.mem_stdL x

theorem om_vac {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {δ : ℂ} {sc : ℝ} (hP : StdPair θ S T δ sc ψ)
    {μ : (AE D)ˣ →* Circle} {om : Om S T} (hW : IsWeilDatumO ψ S T μ μ om)
    (hu : ∀ v ε, GlobalTheory.WeilParts.NonSplitAt D v ε → GlobalTheory.WeilParts.UnramAt ε μ) {f : WO S T → ℂ}
    (hf : IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (intVec D _) (intVec D _) f) {k : GA D S} {k' : GA D T}
    (hk : k ∈ GfC S) (hk' : k' ∈ GfC T) (a : IntG S k) (a' : IntG T k') :
    ∃ x y, IsDetRoot S k x ∧ IsDetRoot T k' y ∧ om (k, k') f = (((μ x)⁻¹ * μ y : Circle) : ℂ) • f := by
  have m := isMov_of_intG a (a.inv hP.gS)
  have m' := isMov_of_intG a' (a'.inv hP.gT)
  have sS := GlobalTheory.Ker.Base.selfDualC_stdL hP.gS
  have sT := GlobalTheory.Ker.Base.selfDualC_stdL hP.gT
  obtain ⟨x, hx, rx⟩ := GlobalTheory.LatticeUnitRoot.exists_finUnit_isDetRoot D S _ sS k hk m
  obtain ⟨y, hy, ry⟩ := GlobalTheory.LatticeUnitRoot.exists_finUnit_isDetRoot D T _ sT k' hk' m'
  have hc : ∀ V : HSp D, V.gram = 1 → ∀ τ, IsCartanInv (gramAt D V τ) 1 := fun V hV τ => by
    have : gramAt D V τ = 1 := by
      unfold gramAt
      rw [hV]
      simp
    rw [this]
    exact GlobalTheory.AdTh.isCartanInv_one_splitStab _
  refine ⟨x, y, rx, ry, GlobalTheory.FinVac.om_vacuum_finite D S T ψ θ hP.inf hP.sigS hP.sigT μ μ om hW
    (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D) (fun v ε hv => ⟨hu v ε hv, hu v ε hv⟩) (fun _ => 1) (fun _ => 1)
    (hc S hP.gS) (hc T hP.gT) _ _ sS sT f ?_ k hk k' hk' m m' x y hx hy rx ry⟩
  rwa [coe_stdL, coe_stdL]

end GlobalTheory.AdForm.StabMove
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowsMemBaseChainStageZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BaseChain

theorem levFn_datY_noQ {D : D7} {V : HSp D} (β : GL (Fin V.rank) (Lev.EAf D)) {r : ℕ} (hn : V.rank ≤ r) (hr : r ≤ V.rank) (t j : ℕ)
    (Pg Q : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (fr : Formalism.IndefR.Lev.Frm) (x : GL (Fin V.rank) (Lev.EAf D)) :
    levFn β (Lev.datY V.rank r t j hr Pg Q P χ ξ fr) x = levFn β (Lev.datY V.rank r t j hr Pg ∅ P χ ξ' fr) x := by
  unfold levFn
  have hq : ∀ PP ∈ (Lev.datY V.rank r t j hr Pg Q P χ ξ fr).Q,
      (Lev.datY V.rank r t j hr Pg Q P χ ξ fr).xq PP
        (dBlk (blk2 (Lev.datY V.rank r t j hr Pg Q P χ ξ fr).r) 1 (redFn β PP x)) = 1 := by
    intro PP _
    show _ = 1
    rw [show (Lev.datY V.rank r t j hr Pg Q P χ ξ fr).r = r from rfl, Formalism.IndefR.Eqv.Act.block_determinant_empty_eq_one hn, map_one]
  rw [Finset.prod_eq_one hq]
  rfl

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

end GlobalTheory.BaseChain

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ListProdMapNeZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

private theorem list_prod_map_pow_eq {α : Type} (l : List α) (f g : α → ℂ) (n : ℕ) (h : ∀ a, f a ^ n = g a ^ n) :
    (l.map f).prod ^ n = (l.map g).prod ^ n := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.prod_cons, mul_pow, ih, h]

private theorem list_prod_map_ne_zero {α : Type} (l : List α) (f : α → ℂ) (h : ∀ a, f a ≠ 0) :
    (l.map f).prod ≠ 0 := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.prod_cons]; exact mul_ne_zero (h a) ih

theorem mono_pow_eq {D : D7} {c : Comm D} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {ι : Type} (o : TDat c k ι) (r : ι → ℝ) (e : ι → ℤ)
    (χ χ' : (AE D)ˣ →* Circle) (n : ℕ) (hn : χ ^ n = χ' ^ n) :
    o.mono r e χ ^ n = o.mono r e χ' ^ n := by
  unfold TDat.mono
  apply list_prod_map_pow_eq
  intro i
  simp only [mul_pow, chrPow]
  congr 1
  have key : ∀ μ : (AE D)ˣ →* Circle, ((μ ((o.p i).idele o.q.unit) ^ e i : Circle) : ℂ) ^ n
      = ((((μ ^ n) ((o.p i).idele o.q.unit)) ^ e i : Circle) : ℂ) := by
    intro μ
    rw [MonoidHom.pow_apply, ← Circle.coe_pow, ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm]
  rw [key χ, key χ', hn]

theorem mono_ne_zero {D : D7} {c : Comm D} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {ι : Type} (o : TDat c k ι) (r : ι → ℝ) (e : ι → ℤ)
    (χ : (AE D)ˣ →* Circle) (hr : ∀ i, 0 < r i) : o.mono r e χ ≠ 0 := by
  unfold TDat.mono
  apply list_prod_map_ne_zero
  intro i
  refine mul_ne_zero ?_ ?_
  · exact_mod_cast (hr i).ne'
  · exact Circle.coe_ne_zero _

theorem mono_unitRatio : ∀ (D : D7) (c : Comm D) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι) (r : ι → ℝ) (e : ι → ℤ) (χ χ' : (AE D)ˣ →* Circle)
    (S : ℕ → Prop), (∀ i, 0 < r i) → (∃ n : ℕ, 0 < n ∧ χ ^ n = χ' ^ n) → UnitRatio S (o.mono r e χ) (o.mono r e χ') := by
  intro D c k _ _ _ _ ι o r e χ χ' S hr ⟨n, hn, hχ⟩
  exact (GlobalTheory.T.isRootOfSUnitRatioUpToRootOfUnity_closure_laws S).2.2.1 _ _ n (mono_ne_zero o r e χ' hr) hn (mono_pow_eq o r e χ χ' n hχ)

end GlobalTheory.SeeSaw
end
