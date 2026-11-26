module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTOntoRep
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.BesselSplit
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.Admissible
public import Formalism.LocalToGlobal.IndefiniteReal.BridgeSeed

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.IsBuiltPlaceOfCompactTest
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

namespace Formalism.L2.SG.Pf.CarrierT

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built Formalism.L2.SG.LocWSOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Choice X θ)

abbrev ITc (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (c : Formalism.FourierDecayAlt.LE.Cut) (i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m0E X C u u' e j *ᵥ nuE X C u' e i0' j)) (A₀ : ℝ) : CarrierIn X u u' :=
  carrierInT X C u u' e he hv CA de de' l grid grid1 fc c (nuE X C u' e i0') (m0E X C u u' e) Θ TP A₀

def plOf (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (c : Formalism.FourierDecayAlt.LE.Cut) (i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m0E X C u u' e j *ᵥ nuE X C u' e i0' j)) (A₀ : ℝ)
    (hN : ParNums (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀))
    (hty : Types (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀)) (hl2 : l + 2 ≤ D.R.k)
    (hΘ : ∀ j : Fin (nfE D),
      ∃ (Xo : Formalism.FourierDecayAlt.Q.ActualOps D.R.k D.R.rS (towersOf X C u u' e j).base.z (towersOf X C u u' e j).base.z'
          (towersOf X C u u' e j).base.π (towersOf X C u u' e j).base.π')
        (μ : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS))
        (L : Formalism.FourierDecayAlt.R.LevelData (Formalism.FourierDecayAlt.Q.Pr (Formalism.FourierDecayAlt.Q.RadSp D.R.k D.R.rS (towersOf X C u u' e j).base.z
          (towersOf X C u u' e j).base.z' (towersOf X C u u' e j).base.π (towersOf X C u u' e j).base.π')) D.R.rS)
        (st : Formalism.FourierDecayAlt.Fr.Start (Formalism.FourierDecayAlt.Q.Pr (Formalism.FourierDecayAlt.Q.RadSp D.R.k D.R.rS (towersOf X C u u' e j).base.z
          (towersOf X C u u' e j).base.z' (towersOf X C u u' e j).base.π (towersOf X C u u' e j).base.π'))),
        Formalism.FourierDecayAlt.P5.IsData (parE e u u' de de' j) (towersOf X C u u' e j).base.z (towersOf X C u u' e j).base.z'
          (towersOf X C u u' e j).base.π (towersOf X C u u' e j).base.π' Xo μ L st (l + 1) ∧
        Formalism.FourierDecayAlt.KB.IsTopLift2 (parE e u u' de de' j) (l + 1) (towersOf X C u u' e j).base L st (Θ j))
    (j : Fin (nfE D)) : Formalism.FourierDecayAlt.KB.Pl (parE e u u' de de' j) (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)) where
  l0 := l + 1
  T := towersOf X C u u' e j
  ν' := nuE X C u' e i0' j
  m₀ := m0E X C u u' e j
  Θ := Θ j
  TP := TP j
  hl := by show 1 ≤ l + 1 ∧ l + 1 ≤ D.R.k ∧ 2 ≤ D.R.k; omega
  hT := towerOf_norm _ _ _ _
  hF := frames_carrierInT X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀ j
  hP := isPlace_of _ hN hty j
  hΘ := hΘ j

theorem isBuiltPlace_of_compact_test (Cb Cc : ℝ) (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (c : Formalism.FourierDecayAlt.LE.Cut) (i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m0E X C u u' e j *ᵥ nuE X C u' e i0' j)) (A₀ : ℝ)
    (hN : ParNums (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀))
    (hty : Types (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀))
    (hcc : CoefCC (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀))
    (hcap : CoefCap (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀))
    (hΘ : ∀ j : Fin (nfE D),
      ∃ (Xo : Formalism.FourierDecayAlt.Q.ActualOps D.R.k D.R.rS (towersOf X C u u' e j).base.z (towersOf X C u u' e j).base.z'
          (towersOf X C u u' e j).base.π (towersOf X C u u' e j).base.π')
        (μ : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS))
        (L : Formalism.FourierDecayAlt.R.LevelData (Formalism.FourierDecayAlt.Q.Pr (Formalism.FourierDecayAlt.Q.RadSp D.R.k D.R.rS (towersOf X C u u' e j).base.z
          (towersOf X C u u' e j).base.z' (towersOf X C u u' e j).base.π (towersOf X C u u' e j).base.π')) D.R.rS)
        (st : Formalism.FourierDecayAlt.Fr.Start (Formalism.FourierDecayAlt.Q.Pr (Formalism.FourierDecayAlt.Q.RadSp D.R.k D.R.rS (towersOf X C u u' e j).base.z
          (towersOf X C u u' e j).base.z' (towersOf X C u u' e j).base.π (towersOf X C u u' e j).base.π'))),
        Formalism.FourierDecayAlt.P5.IsData (parE e u u' de de' j) (towersOf X C u u' e j).base.z (towersOf X C u u' e j).base.z'
          (towersOf X C u u' e j).base.π (towersOf X C u u' e j).base.π' Xo μ L st (l + 1) ∧
        Formalism.FourierDecayAlt.KB.IsTopLift2 (parE e u u' de de' j) (l + 1) (towersOf X C u u' e j).base L st (Θ j))
    (hDD : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.KB.InDDplus2 (parE e u u' de de' j) (l + 1) (towersOf X C u u' e j).base Cb (Θ j))
    (hOk : ∀ w, ((Formalism.L2.SG.SpectralTiesReal.gOf D e).place w).Ok)
    (hw : Formalism.FourierDecayAlt.Sz.IsWord D.R.k de) (hw' : Formalism.FourierDecayAlt.Sz.IsWord D.R.k de') (hl1 : 1 ≤ l) (hl2 : l + 2 ≤ D.R.k)
    (hne : de l ≠ de' l)
    (hG : Formalism.FourierDecayAlt.C.GridsOK (Formalism.L2.SG.Pf.Carrier.sOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀)))
    (hR : Formalism.FourierDecayAlt.KB.GridsRich (Formalism.L2.SG.Pf.Carrier.sOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀)))
    (hL : Formalism.FourierDecayAlt.JCT.LongCut Cc (Formalism.L2.SG.Pf.Carrier.sOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀)))
    (hCA : Cc ≤ CA) (hsm : ∀ j, Formalism.FourierDecayAlt.B.CkOn ⊤ (Formalism.FourierDecayAlt.B.GV D.R.k D.R.rS) (fc j))
    (hA : Cc * ((D.R.rS : ℝ) + 1) ^ 4 *
      (((4 * Formalism.FourierDecayAlt.C.Kst * (D.R.rS + 1) : ℕ) : ℝ) * (2 * (D.R.rS : ℝ) + D.R.k + 1) ^ 2 +
        (2 * (D.R.rS : ℝ) + D.R.k + 1) ^ 3) ≤ A₀) :
    Formalism.FourierDecayAlt.KB.IsLeadingFormPlace Cb Cc (Formalism.L2.SG.Pf.Carrier.sOf (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀))
      (fun j => plOf X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀ hN hty hl2 hΘ j)
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).fc
      (ITc X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀).χ A₀ := by
  obtain ⟨hg1, hg2, hun, ⟨hcut, hbv⟩, hl1', hl2', hG', hL', hCA', -, -, hA', hon⟩ :=
    isBuiltPlace_carrierInT X C Cc u u' e he hv CA de de' l grid grid1 fc c (nuE X C u' e i0')
      (m0E X C u u' e) Θ TP A₀ hN hty (frames_carrierInT X C u u' e he hv CA de de' l grid grid1 fc c i0' Θ TP A₀)
      hcc hcap hw hw' hl1 hl2 hne hG hL hCA hsm hA
  refine ⟨⟨hg1, hg2, hun, hcut, fun v => hOk _, hw, hw', hl1', hl2', hne, hG', hR, hL', hCA', hA',
    fun v => ⟨rfl, hDD v, (hbv v).1, hsm v, (hbv v).2.2.2.2.1⟩⟩, fun v => (hbv v).2.2.2.2.2, hon⟩

end Formalism.L2.SG.Pf.CarrierT
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocUniq
noncomputable section

open MeasureTheory Formalism.MainNotions.S Formalism.MainNotions.CayleySignature
open scoped InnerProductSpace ENNReal

namespace Formalism.L2.SG.Pf.WuDec

section Core

variable {k r : ℕ}

theorem lowSmoothSK {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} {w : H}
    (hds : IsDSHpk k r ε lam σ) (hlow : IsLowUnitH k r ε lam σ w) : w ∈ smoothVecs (k := k) (r := r) σ :=
  Formalism.L2.SG.Pf.k_finite_smooth k r ε lam H σ hds w (PI.UnitaryGroupMassFormula.LowSmooth.isKFinHpk_of_lowUnit hlow)

theorem besselUniq_core (hBW : Formalism.L2.SG.LocWSOf.BesselOfW) (hM1 : Formalism.L2.SG.LitS.BesselMultOne)
    {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {u : Fin k → ℝ} {lam : Fin (2 * r + k + 1) → ℝ}
    {ε : Fin (2 * r + k + 1) → Bool} {h : ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Mat k r → (H →L[ℂ] H)}
    (hl : Formalism.QuantumDeterminants.IsHCParam lam) (hds : IsDSHpk k r ε lam σ) (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam h)
    (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h) (hz : Formalism.QuantumDeterminants.inWb k r z) (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hc : c ≠ 0)
    {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp] {π : Mat k r → (Vp →L[ℂ] Vp)}
    (hπ : IsHCTypeW k r z u π) {w : H} (hw : IsLowUnitH k r ε lam σ w) (hws : w ∈ smoothVecs (k := k) (r := r) σ)
    {μG μW μN ν : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hG : IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG) (hW : IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) (hQ : IsQuotMeas μG (Formalism.MainNotions.S.muS μW μN) ν)
    {W W0 : Mat k r → Vp}
    (hc1 : ContinuousOn W (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))) (he1 : IsSPsiEquiv z (Formalism.QuantumDeterminants.psi k r z c) π W)
    (hr1 : ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => eFun μG σ w (Matrix.of g) • W (x * Matrix.of g)) μG ∧
      rconv μG (eFun μG σ w) W x = W x)
    (hl1 : l2SG ν W ≠ 0) (hl1' : l2SG ν W < ⊤)
    (hc2 : ContinuousOn W0 (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))) (he2 : IsSPsiEquiv z (Formalism.QuantumDeterminants.psi k r z c) π W0)
    (hr2 : ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => eFun μG σ w (Matrix.of g) • W0 (x * Matrix.of g)) μG ∧
      rconv μG (eFun μG σ w) W0 x = W0 x)
    (hl2 : l2SG ν W0 ≠ 0) (hl2' : l2SG ν W0 < ⊤)
    (hx0 : ∃ x0 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), W0 x0 ≠ 0) :
    ∃ a : ℂ, ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), W x = a • W0 x := by
  obtain ⟨B, hB, hWB⟩ := hBW k r z c u lam ε h H σ hl hds hg hok hz hT hc Vp π hπ w hw μG μW μN ν hG hW hN hQ
    W hc1 he1 hr1 hl1 hl1'
  obtain ⟨B0, hB0, hW0B⟩ := hBW k r z c u lam ε h H σ hl hds hg hok hz hT hc Vp π hπ w hw μG μW μN ν hG hW hN hQ
    W0 hc2 he2 hr2 hl2 hl2'
  rw [Formalism.L2.SG.LitS.psi_eq_psiGen] at hB hB0
  obtain ⟨a, b, hab, hlin⟩ := hM1 k r ε lam H σ z (fun _ => c) u Vp π hl hds hz hT (fun _ => hc) hπ B B0 hB hB0
  have hsm : ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), σ x w ∈ smoothVecs (k := k) (r := r) σ :=
    fun x hx => Formalism.L2.SG.BesselSplit.smooth_translate_ds hds hws hx
  by_cases ha : a = 0
  · exfalso
    have hb : b ≠ 0 := hab.resolve_left (not_not.2 ha)
    obtain ⟨x0, hx0U, hx0W⟩ := hx0
    have h1 := hlin (σ x0 w) (hsm x0 hx0U)
    rw [ha, zero_smul, zero_add] at h1
    have h2 : B0 (σ x0 w) = 0 := (smul_eq_zero.1 h1).resolve_left hb
    exact hx0W (by rw [hW0B x0 hx0U, h2])
  · refine ⟨-(b / a), fun x hx => ?_⟩
    have h1 := hlin (σ x w) (hsm x hx)
    rw [hWB x hx, hW0B x hx]
    have : a • B (σ x w) = -(b • B0 (σ x w)) := eq_neg_of_add_eq_zero_left h1
    calc B (σ x w) = a⁻¹ • (a • B (σ x w)) := by rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
      _ = -(b / a) • B0 (σ x w) := by
          rw [this, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]

end Core

end Formalism.L2.SG.Pf.WuDec
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyFinal
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyTie
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
open Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups

namespace Formalism.L2.SG.Pf.Carrier.EnergyPf

open Formalism.L2.SG.AdBridge Formalism.L2.SG.SpectralTiesReal Formalism.L2.SG.Pf.Carrier

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (Y : Full X) (u u' : D.what₂.Word)
  (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

theorem intN_massDataY : (massDataY X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).IntN = IntNX X u u' ψ := rfl

end Formalism.L2.SG.Pf.Carrier.EnergyPf
end
end

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Classical
open Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full

namespace Formalism.L2.SG.Pf.Carrier.EnergyFinal

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.EnergyCut Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.EnergyPf
  Formalism.L2.SG.Pf.Carrier.EnergyPlace Formalism.L2.SG.AdBridge Formalism.L2.SG.SpectralTiesReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {u u' : D.what₂.Word}

def PlaceNormG (P : Parts X u u') (hr : P.S.G.r = D.R.rS) : Prop :=
  ∀ (v : InfinitePlace X.B.I.F) (g : Formalism.REAL.UJ (X.B.I.ε v)) (cv : Fin (D.R.rS + 1) → ℂ), cv ∈ GoodV u u' →
    Zhat (X.B.I.ε v) (frm X u 1 v) (frm X u' 1 v) (uMat g) = Matrix.diagonal cv →
    hs2 (JvX X u u' v g) =
      ‖Formalism.FourierDecayAlt.B.hsVec (Formalism.FourierDecayAlt.B.JF (P.T (P.τ.symm v)).base (P.f (P.τ.symm v))
        (Formalism.FourierDecayAlt.B.gq (P.T (P.τ.symm v)).base (phiQ P hr cv)))‖ ^ 2

theorem placeNorm_of_G (P : Parts X u u') (hr : P.S.G.r = D.R.rS) (hG : PlaceNormG P hr)
    (L : InfinitePlace X.B.I.F → (Fin (D.R.rS + 1) → ℂ) → ℝ) (hL : LocRep X u u' L) : PlaceNorm P hr L := by
  intro v cv hcv
  let c : Cinf X := fun _ => cv
  have hc : c ∈ Good X u u' := fun _ => hcv
  obtain ⟨γ, hγ⟩ := InfCut.ProductExactness.StepReal_holds D X u u' 1 one_pos c hc
  have hex : ∃ γ, HasDiag X u u' 1 c γ := ⟨γ, hγ⟩
  have hd : HasDiag X u u' 1 c (hOf X u u' 1 c) := by
    unfold hOf
    rw [dite_eq_left hex]
    exact hex.choose_spec
  have h1 : hs2 (JvX X u u' v ((hOf X u u' 1 c) v)) = L v cv := hL.2 c hc v
  have h2 := hG v ((hOf X u u' 1 c) v) cv hcv (hd v)
  exact h1.symm.trans h2

end Formalism.L2.SG.Pf.Carrier.EnergyFinal
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTOntoExt
noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.RowDict Formalism.MainNotions.LeviCoordinates Formalism.L2.Theta

namespace Formalism.L2.SG.EvalTOntoExt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)


theorem instances : SigmaFinite (X.B.I.muA X.B.μf) ∧ (X.B.I.muA X.B.μf).IsMulLeftInvariant ∧
    (X.B.I.muA X.B.μf).IsMulRightInvariant := by
  have := X.B.sf
  have := X.B.haar
  have := Formalism.L2.SG.Pf.muf_right X
  exact ⟨rr_muA_sigmaFinite X.B.I X.B.μf, rr_muA_left X.B.I X.B.μf, rr_muA_right X.B.I X.B.μf⟩

end Formalism.L2.SG.EvalTOntoExt

end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarPinVtLZero
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

namespace Formalism.L2.SG.Pf.Carrier.CarPinVt

open Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def GNonNeg (u u' : D.what₂.Word) : Prop :=
  ∀ (w : Point D.host.E (D.R.rS + 1)) (γ : X.B.I.Ginf), IsPtRep X u u' w γ → ∀ v, 0 ≤ GX X u u' D.host.rdE γ v

theorem lZero_of (u u' : D.what₂.Word) (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (FdN FdN' : Set X.B.I.Ginf) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (hG : GNonNeg X u u') :
    LZero X u u' sc i0 i0' FdN FdN' νq := by
  intro p w hp hng
  unfold VtPt
  rw [hp]
  simp only
  by_cases hrep : ∃ γ, IsPtRep X u u' w γ
  · have h1 : ¬ ∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v := fun h => hng ⟨hrep, h⟩
    push_neg at h1
    obtain ⟨v, hv⟩ := h1
    have hrepw : IsPtRep X u u' w (gamW X u u' w) := by
      unfold gamW; rw [dite_eq_left hrep]; exact hrep.choose_spec
    have h0 : GX X u u' D.host.rdE (gamW X u u' w) v = 0 := le_antisymm hv (hG w _ hrepw v)
    have hk := Formalism.MainNotions.BridgeLemma.five_le_k D
    have hn : nW X u u' w = 0 := by
      unfold nW
      refine Finset.prod_eq_zero (Finset.mem_univ v) ?_
      rw [h0, zero_pow (by omega), zero_mul]
    rw [hn, Real.sqrt_zero, Complex.ofReal_zero, zero_smul]
  · have hV : unscaledOperatorAtPointRepresentative X u u' sc i0 i0' νq w = 0 := by
      unfold unscaledOperatorAtPointRepresentative; rw [if_neg hrep]
    rw [hV, map_zero, smul_zero]

theorem gX_nonneg {θ : ℝ} (C : Formalism.L2.SG.LocWSOf.Choice X θ) (u u' : D.what₂.Word) (γ : X.B.I.Ginf)
    (v : InfinitePlace X.B.I.F) : 0 ≤ GX X u u' D.host.rdE γ v := by
  obtain ⟨hQ1, hQ2, hQ3, hQ4⟩ := Formalism.L2.SG.Pf.CarrierT.isTransp_Qcs X C v
  set Qm := Formalism.L2.SG.LocWSOf.Qcs C (X.pl v)
  set Qim := Formalism.L2.SG.LocWSOf.Qics C (X.pl v)
  set gg : ℕ := D.host.g 0 * D.host.g 1
  have hTr : Bridge.TrHyp (Formalism.L2.SG.RealObj.InfCut.PtRepPf.frU X u v) Qm Qim (fun a : Fin D.R.rS => cTor (gg : ℝ) D.R.rS a) :=
    ⟨hQ1, hQ2, hQ3, fun a => (hQ4 a a rfl).1, fun a => (hQ4 a a rfl).2⟩
  have hTr' : Bridge.TrHyp (Formalism.L2.SG.RealObj.InfCut.PtRepPf.frU X u' v) Qm Qim (fun a : Fin D.R.rS => cTor (gg : ℝ) D.R.rS a) :=
    ⟨hQ1, hQ2, hQ3, fun a => (hQ4 a a rfl).1, fun a => (hQ4 a a rfl).2⟩
  have hrd := Formalism.MainNotions.LocalModelPeriodLattices.rdE_pos D
  have hz := Formalism.L2.SG.Pf.BaseOf.zc_spec X C u v
  have hz' := Formalism.L2.SG.Pf.BaseOf.zc_spec X C u' v
  have hgv := Bridge.delta_GV hTr (Formalism.L2.SG.Pf.Carrier.uMat_unitary (γ v))
  have hG := Formalism.QuantumDeterminants.gNonneg D.R.k D.R.rS _ _ hz.1 hz'.1 (Formalism.L2.SG.Pf.BaseOf.zc_pos X C u v)
    (Formalism.L2.SG.Pf.BaseOf.zc_pos X C u' v) _ hgv
  have h1 := Bridge.zhat_cs hTr hTr' (sc := D.host.rdE) hrd.ne' (Formalism.MainNotions.S.uMat (γ v))
  set Zr := Formalism.L2.SG.RealObj.Zhat (X.B.I.ε v)
    (famSc D.host.rdE (Formalism.L2.SG.RealObj.InfCut.PtRepPf.frU X u v).e (Formalism.L2.SG.RealObj.InfCut.PtRepPf.frU X u v).z)
    (famSc D.host.rdE (Formalism.L2.SG.RealObj.InfCut.PtRepPf.frU X u' v).e (Formalism.L2.SG.RealObj.InfCut.PtRepPf.frU X u' v).z)
    (Formalism.MainNotions.S.uMat (γ v)) with hZr
  have h1' : Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (Formalism.L2.SG.Pf.BaseOf.zc X C u v) (Formalism.L2.SG.Pf.BaseOf.zc X C u' v)
      (Qim * Formalism.MainNotions.S.uMat (γ v) * Qm) =
      Matrix.diagonal (fun a => star (Bridge.lam (fun a : Fin D.R.rS => cTor (gg : ℝ) D.R.rS a) D.host.rdE a)) * Zr *
        Matrix.diagonal (Bridge.lam (fun a : Fin D.R.rS => cTor (gg : ℝ) D.R.rS a) D.host.rdE) := h1
  unfold Formalism.QuantumDeterminants.Gf Formalism.QuantumDeterminants.Dmin at hG
  rw [hz.2, hz'.2, h1'] at hG
  have hgg0 : (0 : ℝ) < gg := by
    show (0 : ℝ) < ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ)
    exact_mod_cast Nat.mul_pos (Formalism.L2.SG.Pf.CarrierSz.g_pos D).1 (Formalism.L2.SG.Pf.CarrierSz.g_pos D).2
  set κ : ℂ := -Complex.I * (((gg : ℝ) / (2 * Real.pi) : ℝ) : ℂ) with hκ
  have hc : ∀ a : Fin D.R.rS, cTor (gg : ℝ) D.R.rS a = κ ^ (D.R.rS - a.val) := by
    intro a; unfold cTor; congr 1; rw [hκ]; push_cast; field_simp
  have hκ0 : κ ≠ 0 := by
    rw [hκ]; refine mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) ?_
    exact_mod_cast (div_pos hgg0 (by positivity)).ne'
  have hlamne : ∀ a : Fin (D.R.rS + 1), Bridge.lam (fun a : Fin D.R.rS => cTor (gg : ℝ) D.R.rS a) D.host.rdE a ≠ 0 := by
    intro a h0
    have := (Bridge.cS_lam hc hrd.ne' a).1
    rw [h0, mul_zero] at this
    exact pow_ne_zero _ hκ0 this.symm
  have hlast : Bridge.lam (fun a : Fin D.R.rS => cTor (gg : ℝ) D.R.rS a) D.host.rdE (Fin.last D.R.rS) = 1 := by
    have := (Bridge.cS_lam hc hrd.ne' (Fin.last D.R.rS)).1
    have hcl : Formalism.L2.SG.Pf.CarrierTop.cS D.R.rS D.host.rdE (Fin.last D.R.rS) = 1 := by
      simp [Formalism.L2.SG.Pf.CarrierTop.cS]
    rw [hcl, one_mul] at this
    rw [this]; simp
  have hD1 : ∀ M : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ,
      (M.submatrix (Fin.castLE (Nat.le_of_lt_succ (Fin.last (D.R.rS + 1)).isLt))
        (Fin.castLE (Nat.le_of_lt_succ (Fin.last (D.R.rS + 1)).isLt))).det = RealObj.Dl M (D.R.rS + 1) :=
    fun M => by unfold RealObj.Dl; rw [dite_eq_left le_rfl]
  have hD2 : ∀ M : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ,
      (M.submatrix (Fin.castLE (Nat.le_of_lt_succ (⟨D.R.rS, by omega⟩ : Fin (D.R.rS + 2)).isLt))
        (Fin.castLE (Nat.le_of_lt_succ (⟨D.R.rS, by omega⟩ : Fin (D.R.rS + 2)).isLt))).det = RealObj.Dl M D.R.rS :=
    fun M => by unfold RealObj.Dl; rw [dite_eq_left (Nat.le_succ _)]
  rw [hD1, hD2, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hG
  have hGd := Bridge.G_diag D.R.rS Zr
    (fun a => star (Bridge.lam (fun a : Fin D.R.rS => cTor (gg : ℝ) D.R.rS a) D.host.rdE a))
    (Bridge.lam (fun a : Fin D.R.rS => cTor (gg : ℝ) D.R.rS a) D.host.rdE) (Tr D u * Tr D u') (by rw [hlast]; simp)
  rw [hGd] at hG
  have hne1 : (∏ i : Fin D.R.rS, star (Bridge.lam (fun a : Fin D.R.rS => cTor (gg : ℝ) D.R.rS a) D.host.rdE
      (Fin.castLE (Nat.le_succ D.R.rS) i))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => star_ne_zero.mpr (hlamne _)
  have hne2 : (∏ i : Fin D.R.rS, Bridge.lam (fun a : Fin D.R.rS => cTor (gg : ℝ) D.R.rS a) D.host.rdE
      (Fin.castLE (Nat.le_succ D.R.rS) i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => hlamne _
  have hpos := pow_pos (mul_pos (norm_pos_iff.mpr hne1) (norm_pos_iff.mpr hne2)) 2
  have := (mul_nonneg_iff_of_pos_left hpos).mp hG
  unfold GX Gv
  exact this

theorem lZero_of_choice {θ : ℝ} (C : Formalism.L2.SG.LocWSOf.Choice X θ) (u u' : D.what₂.Word) (sc : ℝ)
    (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (FdN FdN' : Set X.B.I.Ginf)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf) : LZero X u u' sc i0 i0' FdN FdN' νq :=
  lZero_of X u u' sc i0 i0' FdN FdN' νq fun _ γ _ v => gX_nonneg X C u u' γ v

end Formalism.L2.SG.Pf.Carrier.CarPinVt
end
end
