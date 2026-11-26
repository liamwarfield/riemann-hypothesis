module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FamRaise
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsFinal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuotMeas

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DegenerateConstant
noncomputable section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma Formalism.MainNotions.BridgeLemma₂

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Formalism.L2.SG.RowsU

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure UC where
  c3 : ℝ
  cH : ℝ
  cV : ℝ
  cS : ℝ
  c4 : ℝ
  CaF : ℝ → ℝ
  secondOrderBound : ℝ → ℝ
  ChF : ℝ → ℝ

def c0ND (CT A C0 : ℝ) (U : UC) : ℝ :=
  let c := max (max U.c3 1) (max (|U.cH| + 2) (|U.cV| + 2))
  max c (4 + (c ^ 2 + 2 * max (U.ChF (9 * c + 3) - c) 0) * (6 * c + 2))

def degenerateConstant (CT : ℝ) (U : UC) : ℝ :=
  let c := max (max (max U.c3 (max (max 1 CT) (|U.cH| + 2))) 1) (max (|U.cH| + 2) (|U.cV| + 2))
  max (max c (4 + (c ^ 2 + 2 * max (U.ChF (9 * c + 3) - c) 0) * (6 * c + 2)))
    (max (2 * U.secondOrderBound (9 * c + 3)) |U.CaF (9 * c + 3)|)

def corankOneConstant (CT A C0 CGam : ℝ) (U : UC) : ℝ :=
  let c := max (max U.c3 1) (max (max (|U.cH| + 2) (|U.cV| + 2)) (max (|U.cS| + 2) (|U.c4| + 2)))
  max (max (4 * Real.sqrt A) (2 * Real.sqrt (2 * C0) * c))
    (max (CGam + U.secondOrderBound (9 * c + 3)) (4 + 2 * (c ^ 2 + 2 * max (U.ChF (9 * c + 3) - c) 0) * (c + 1)))

section Fam

variable {eps : ℝ} (Fm : FamP eps) (C1 : ℝ) (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1)
  (Cg cb Cu cT CT C0 A : ℝ)

def UAdm (U : UC) : Prop :=
  (∀ C ≥ U.c3, OwnEv Fm fun C' Cl x i => ∀ u u',
    VanishingOnXAndXPlus.adm20 (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A 3 C) ∧
  (OwnEv Fm fun C' Cl x i => ∀ u u', VanishingOnXAndXPlus.HerrCocycleExtensionClass (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A U.cH) ∧
  (OwnEv Fm fun C' Cl x i => ∀ (hx : Fm.x1 < x) u u',
    VanishingOnXAndXPlus.TermVolumeSmallCellBound (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1 (Y x hx i u u') C' Cl Cg cb Cu cT CT C0 A U.cV) ∧
  (OwnEv Fm fun C' Cl x i => ∀ u u', VanishingOnXAndXPlus.ArchimedeanSignatureMatching (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A U.cS) ∧
  (OwnEv Fm fun C' Cl x i => ∀ u u', VanishingOnXAndXPlus.adm21 (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A U.c4) ∧
  ∀ Cpr : ℝ, 0 ≤ U.ChF Cpr ∧ 0 ≤ U.CaF Cpr ∧ ∀ δ > 0, OwnEv Fm fun C' Cl x i =>
    VanishingOnXAndXPlus.AmplitudeBoundsConjunction (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 A C1 Cpr (U.CaF Cpr) (U.secondOrderBound Cpr) (U.ChF Cpr) δ

theorem rowsKBU (U : UC) (hU : UAdm Fm C1 X Y Cg cb Cu cT CT C0 A U) :
    ∀ c ≥ max (max 1 CT) (|U.cH| + 2), OwnEv Fm fun C' Cl x i => ∀ (hx : Fm.x1 < x) u u',
      Cnt.Hyp (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A → rows_KBound (Y x hx i u u') c := by
  intro c hc
  obtain ⟨_, h27, _⟩ := hU
  refine OwnEv.mono ?_ h27
  intro C' Cl x i h hx u u' hH
  have hc1 : 1 ≤ c := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hc
  have hCT : CT ≤ c := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hc
  have hcH : |U.cH| + 2 ≤ c := le_trans (le_max_right _ _) hc
  exact rows_KBound_of (Y x hx i u u') hH (rows_stHH_mono (by linarith [le_abs_self U.cH])
    (by linarith [neg_abs_le U.cH]) (h u u')) hc1 hCT

def c0U (CT A C0 CGam : ℝ) (U : UC) : ℝ := max (c0ND CT A C0 U) (max (degenerateConstant CT U) (corankOneConstant CT A C0 CGam U))

end Fam

end Formalism.L2.SG.RowsU
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyPlace
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal

namespace Formalism.L2.SG.Pf.Carrier.EnergyPlace

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.EnergyCut Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.EnergyPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

def lamA (P : Parts X u u') (a : Fin P.S.G.r) : ℝ := ((P.S.g : ℝ) / (2 * Real.pi)) ^ (2 * (P.S.G.r - a.val))

def phiQ (P : Parts X u u') (hr : P.S.G.r = D.R.rS) (cv : Fin (D.R.rS + 1) → ℂ) : (Fin P.S.G.r → ℂ) × ℂ :=
  (fun a => ((lamA P a : ℝ) : ℂ) * cv ⟨a.val, by have := a.2; omega⟩, cv ⟨D.R.rS, by omega⟩)

def K0 (P : Parts X u u') : ℝ :=
  2 ^ (P.S.G.r + 1) * ∏ a : Fin P.S.G.r, (lamA P a ^ (2 * (Formalism.QuantumDeterminants.Mdim P.S.G.k P.S.G.r a - 1)))⁻¹

def PlaceNorm (P : Parts X u u') (hr : P.S.G.r = D.R.rS)
    (L : InfinitePlace X.B.I.F → (Fin (D.R.rS + 1) → ℂ) → ℝ) : Prop :=
  ∀ v, ∀ cv ∈ GoodV u u', L v cv =
    ‖Formalism.FourierDecayAlt.B.hsVec (Formalism.FourierDecayAlt.B.JF (P.T (P.τ.symm v)).base (P.f (P.τ.symm v))
      (Formalism.FourierDecayAlt.B.gq (P.T (P.τ.symm v)).base (phiQ P hr cv)))‖ ^ 2

def ChangeVar (P : Parts X u u') (hr : P.S.G.r = D.R.rS) : Prop :=
  P.S.G.k = D.R.k →
    (∀ v, Formalism.QuantumDeterminants.Tz P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z = Tw (D := D) u ∧
      Formalism.QuantumDeterminants.Tz P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z' = Tw (D := D) u') →
    ∀ v (F : (Fin P.S.G.r → ℂ) × ℂ → ℝ), (∀ q, 0 ≤ F q) →
      ∫⁻ cv in GoodV u u', ENNReal.ofReal (wtV u u' cv * F (phiQ P hr cv)) ∂(dcV (D := D)) =
        ENNReal.ofReal (K0 P) * ∫⁻ q, ENNReal.ofReal (Formalism.QuantumDeterminants.bcWeight P.S.G.k P.S.G.r
          (Formalism.QuantumDeterminants.Tz P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z)
          (Formalism.QuantumDeterminants.Tz P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z') q * F q)

def KMatch (P : Parts X u u') : Prop :=
  (P.S.g : ℝ) = ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) → Formalism.FourierDecayAlt.S6.rd D.host.E = D.host.rdE → P.S.G.r = D.R.rS →
    P.S.G.k = D.R.k → 0 < P.S.g → 1 ≤ P.S.G.k → K0 P = EnergyConst.Kexp P

end Formalism.L2.SG.Pf.Carrier.EnergyPlace
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ConstPinOfStd
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier.EnergyConst2

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.EnergyPf Formalism.L2.SG.Pf.Carrier.EnergyConst

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}


variable (X u u') in
def LemmaMSStd (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) : Prop :=
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ → Formalism.L2.SG.LocVol.IsStdChar ψ → Formalism.L2.SG.LocVol.ProdConv X u u' ψ →
    LemmaMS X u u' ψ

end Formalism.L2.SG.Pf.Carrier.EnergyConst2
end
end
