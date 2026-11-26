module

public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.AmplitudeOrbitalIntegral
public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.DoubleCosetBesselBoundOfGapConstantLe
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocQuad1GHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RealObjInInfinityXOfG

@[expose] public section

section -- merged from CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.LocQuad1GHolds
section -- merged from CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.EClose
section -- merged from CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.EFinal
section -- merged from CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.WeilPairJ
section -- merged from CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.StepIntGOf
section -- merged from CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.LocDDQ
section -- merged from CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.Inputs2Of
namespace CompanionTheory.Lime.BM

def Inputs2 : Prop := Formalism.FourierDecayAlt.ThreeDimData.DecLow ∧ Formalism.FourierDecayAlt.ThreeDimData.DecInf ∧ PI.KFinSmooth ∧ UniqGap

theorem inputs2_of (h : UniqGap) : Inputs2 := ⟨inputs.1, inputs.2.1, inputs.2.2.1, h⟩

end CompanionTheory.Lime.BM
end

noncomputable section

open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice

open Formalism.L2.SG.Pf.WuBL

open scoped InnerProductSpace ENNReal

namespace Formalism.L2.SG.RealObj.EnergyIntQ

namespace BM

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

theorem locDDQ (hI : CompanionTheory.Lime.BM.Inputs2) (hRT : ReproTr) (hL2 : L2RightTranslation) (hGp : GapOfHyp)
    (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) (C : Choice X θ) (hLF : LocFactor C) (u : D.what₂.Word)
    (τ : D.what₂.Tau) :
    ∃ (l : X.B.H (vOf X τ) → X.Vloc u (vOf X τ)) (a : ℂ),
      (∀ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp (sigB X (C.Q τ) (C.Qi τ) τ) (v0Of C τ),
        ∀ y ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp (sigB X (C.Q τ) (C.Qi τ) τ) (v0Of C τ),
          Formalism.FourierDecayAlt.ThreeDimData.be (zB X (C.Qi τ) u τ) (cS D) (piB X (C.Q τ) (C.Qi τ) u τ) (sigB X (C.Q τ) (C.Qi τ) τ)
            (C.muW u τ) (muNB D θ) x y = (innerSL ℂ (l y)).smulRight (l x)) ∧
      ∀ γ, X.Wloc u (vOf X τ) γ = a • l (X.B.σ (vOf X τ) (uMat γ) (X.B.w (vOf X τ))) := by
  obtain ⟨h, hHC, hDS', hgap, hok, hz, hT, hc, hty, hlow, hμG, hμW, hμN, hq, hWc, hWe, hWr, hne, hfin⟩ :=
    sideQ hRT hL2 hGp hG hLF (fun u τ => Formalism.L2.SG.Pf.colsTypeTr C u τ) u τ
  have hSide : Formalism.FourierDecayAlt.ThreeDimData.Side D.R.k D.R.rS (epsSH D.R) (lamD D τ) h (sigB X (C.Q τ) (C.Qi τ) τ) (v0Of C τ)
      (zB X (C.Qi τ) u τ) (cS D) (fun i => ((D.hcW u τ).u i : ℝ)) (piB X (C.Q τ) (C.Qi τ) u τ) (C.muW u τ) (muNB D θ)
      (muGB X (C.Q τ) (C.Qi τ) τ) (C.nuS u τ) :=
    ⟨hHC, hDS', hgap, hok, hlow, hz, hT, hc, hty, hμW, hμN, hμG, hq⟩
  obtain ⟨x0, hx0, y0, hy0, hbe⟩ := CompanionTheory.D.Upq.BesselFunctionalConstruction.bessel_nonvanishing_L2 CompanionTheory.Lime.BM.inputs Formalism.FourierDecayAlt.P.schur_hermitian D.R.k D.R.rS
    (epsSH D.R) (lamD D τ) h _ _ (v0Of C τ) _ _ (cS D) _ _ _ _ _ _ hSide _ hWc hWe hWr (pos_iff_ne_zero.mpr hne) hfin
  obtain ⟨l, hl, ⟨x1, hx1, hlx1⟩, hbel⟩ := CompanionTheory.Lime.BM.shape hI.2.2.2 CompanionTheory.Lime.BM.inputs D.R.k D.R.rS (epsSH D.R) (lamD D τ) h _ _
    (v0Of C τ) _ _ (cS D) _ _ _ _ _ _ hSide ⟨x0, hx0, y0, hy0, hbe⟩
  have hWB : WuBessel C := wuBesselOfLoc hRT hL2 hGp C hG
    Formalism.MainNotions.BridgeCS3dBOW.besselOfW_holds hLF (fun τ => Formalism.L2.SG.Pf.dsTr C τ)
    (fun τ => Formalism.L2.SG.Pf.haarTr C τ) (fun u τ => Formalism.L2.SG.Pf.colsTypeTr C u τ)
  obtain ⟨B, hB, hWB'⟩ := hWB u τ
  have hDDs := Formalism.FourierDecayAlt.P.DDSmoothness.DD_smooth hI.2.2.1 hHC hDS' hlow
  have hB' : PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) (zB X (C.Qi τ) u τ)
      (PI.BesselMapUniq.psiGen D.R.k D.R.rS (zB X (C.Qi τ) u τ) (fun _ => cS D)) (sigB X (C.Q τ) (C.Qi τ) τ)
      (piB X (C.Q τ) (C.Qi τ) u τ) B := by
    rw [psiGen_const']; exact (Formalism.MainNotions.BridgeCS3d.isBesselMapSm_iff _ _ _ _ B).1 hB
  have hl' : PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) (zB X (C.Qi τ) u τ)
      (PI.BesselMapUniq.psiGen D.R.k D.R.rS (zB X (C.Qi τ) u τ) (fun _ => cS D)) (sigB X (C.Q τ) (C.Qi τ) τ)
      (piB X (C.Q τ) (C.Qi τ) u τ) l := by
    rw [psiGen_const']; exact hl
  obtain ⟨a, b, hab, hlin⟩ := hI.2.2.2 D.R.k D.R.rS (epsSH D.R) (lamD D τ) h _ (sigB X (C.Q τ) (C.Qi τ) τ)
    (zB X (C.Qi τ) u τ) (fun _ => cS D) (fun i => ((D.hcW u τ).u i : ℝ)) _ (piB X (C.Q τ) (C.Qi τ) u τ)
    hok.1 hgap hok.2.1 hHC hDS' hz hT
    (fun _ => hc) hty B l hB' hl'
  have ha : a ≠ 0 := by
    intro ha0
    have hb : b ≠ 0 := hab.resolve_left (fun h => h ha0)
    apply hlx1
    have := hlin x1 (hDDs x1 hx1)
    rw [ha0, zero_smul, zero_add] at this
    exact (smul_eq_zero.mp this).resolve_left hb
  refine ⟨l, -(b / a), fun x hx y hy => hbel x (hDDs x hx) y hy, fun γ => ?_⟩
  rw [hWB' γ]
  have hsm := hDDs _ (mem_DD C τ γ)
  have h0 := hlin _ hsm
  have e : B (X.B.σ (vOf X τ) (uMat γ) (X.B.w (vOf X τ))) =
      a⁻¹ • (a • B (X.B.σ (vOf X τ) (uMat γ) (X.B.w (vOf X τ)))) := by
    rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
  rw [e, eq_neg_of_add_eq_zero_left h0, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]

end BM

end Formalism.L2.SG.RealObj.EnergyIntQ
end
end

noncomputable section

open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice

open Formalism.L2.SG.RealObj.EnergyIntTor Formalism.L2.SG.Pf.WuBL

open scoped InnerProductSpace ENNReal

namespace Formalism.L2.SG.RealObj.EnergyIntLoc

namespace BM

variable {k r : ℕ}

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

theorem locOrbG_of (hI : CompanionTheory.Lime.BM.Inputs2) (hRT : ReproTr) (hL2 : L2RightTranslation) (hGp : GapOfHyp)
    (hLF : ∀ (D : D7), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (X : HidaSetting D) (θ : ℝ) (C : Choice X θ), LocFactor C) :
    Formalism.L2.SG.RealObj.EnergyInt.LocOrbG := by
  intro D hG X u u' sc hsc c hc γ hγ v
  obtain ⟨τ, rfl⟩ : ∃ τ, v = vOf X τ := ⟨X.pl v, (X.pl.symm_apply_apply v).symm⟩
  have : Nonempty D.what₂.Word := ⟨u⟩
  obtain ⟨C⟩ := Formalism.L2.SG.Pf.choiceExists X 1 one_pos
  obtain ⟨l, a, hbe, hW⟩ := Formalism.L2.SG.RealObj.EnergyIntQ.BM.locDDQ hI hRT hL2 hGp hG C (hLF D hG X 1 C) u τ
  obtain ⟨l', a', hbe', hW'⟩ := Formalism.L2.SG.RealObj.EnergyIntQ.BM.locDDQ hI hRT hL2 hGp hG C (hLF D hG X 1 C) u' τ
  have h1 := (transpC' C τ).1
  have h2 := (transpC' C τ).2.1
  have hg := (transpC' C τ).2.2.1
  obtain ⟨P, hP⟩ := Formalism.MainNotions.S.Inh.obj_cayleyU_rows D
  obtain ⟨yc, hyc, hycl⟩ := y_exists (n_eq' X) (X.B.I.ε (vOf X τ)) (epsSH D.R)
    (fun i => by rw [X.eps_eq]; exact congrArg (epsS D.R) (Fin.ext rfl))
    (X.B.lam (vOf X τ)) (lamD D τ)
    (fun i => by
      rw [X.lam_eq, show X.pl (vOf X τ) = τ from X.pl.apply_symm_apply τ]
      exact congrArg (lamS D.R (D.hc τ)) (Fin.ext rfl))
    (X.B.σ (vOf X τ)) (X.ds (vOf X τ)).2.2.1 (X.low (vOf X τ)).2 (Qcs C τ) (Qics C τ) h2 hg P hP
  set σc := sigB X (Qcs C τ) (Qics C τ) τ with hσc
  set w0 := σc yc (X.B.w (vOf X τ)) with hw0
  have hlow : IsLowUnitH D.R.k D.R.rS (epsSH D.R) (lamD D τ) σc w0 := by
    refine ⟨P, hP, ?_, hycl⟩
    rw [hw0, sigC_norm C τ hyc]
    exact (X.low (vOf X τ)).1
  obtain ⟨h, hgap, hok⟩ := hGp D hG τ
  obtain ⟨νq, hS⟩ := sideC C one_pos u τ hgap hok hlow
  obtain ⟨νq', hS'⟩ := sideC C one_pos u' τ hgap hok hlow
  have hμW := C.muW_haar u τ
  have hμW' := C.muW_haar u' τ
  have : SigmaFinite (C.muW u τ) := hμW.1
  have : SigmaFinite (C.muW u' τ) := hμW'.1
  have : SigmaFinite (muNB D 1) :=
    (Formalism.MainNotions.BridgeCSB.haarLieN _ _ _ (kapN_ne_zero D one_pos) (kapN_ne_top D 1)).1

  have hl : ∀ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp σc w0, ∀ y ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp σc w0,
      Formalism.FourierDecayAlt.ThreeDimData.be (Dc C one_pos u u' τ).z Formalism.QuantumDeterminants.cStd (Dc C one_pos u u' τ).π σc (Dc C one_pos u u' τ).μW
        (Dc C one_pos u u' τ).μN x y = (innerSL ℂ (l y)).smulRight (l x) := by
    intro x hx y hy
    show Formalism.FourierDecayAlt.ThreeDimData.be (zB X (C.Qi τ) u τ) Formalism.QuantumDeterminants.cStd (piB X (Qcs C τ) (Qics C τ) u τ) σc (C.muW u τ)
      ((muNB D 1).map (conjE (Formalism.L2.SG.Pf.muT_ne D))) x y = _
    rw [← scale_eq D, be_tor (Formalism.L2.SG.Pf.muT_ne D) (zT C u τ).1 (cS D) (piB X (C.Q τ) (C.Qi τ) u τ)
      (piB X (Qcs C τ) (Qics C τ) u τ) (sigB X (C.Q τ) (C.Qi τ) τ) σc (sigC_eq C τ)
      (fun _ hh => piC_eq C u τ hh) (C.muW u τ) (muNB D 1) hμW.2.2.1 x y]
    exact hbe x (dd_sub C τ hyc hx) y (dd_sub C τ hyc hy)
  have hl' : ∀ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp σc w0, ∀ y ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp σc w0,
      Formalism.FourierDecayAlt.ThreeDimData.be (Dc C one_pos u u' τ).z' Formalism.QuantumDeterminants.cStd (Dc C one_pos u u' τ).π' σc (Dc C one_pos u u' τ).μW'
        (Dc C one_pos u u' τ).μN x y = (innerSL ℂ (l' y)).smulRight (l' x) := by
    intro x hx y hy
    show Formalism.FourierDecayAlt.ThreeDimData.be (zB X (C.Qi τ) u' τ) Formalism.QuantumDeterminants.cStd (piB X (Qcs C τ) (Qics C τ) u' τ) σc (C.muW u' τ)
      ((muNB D 1).map (conjE (Formalism.L2.SG.Pf.muT_ne D))) x y = _
    rw [← scale_eq D, be_tor (Formalism.L2.SG.Pf.muT_ne D) (zT C u' τ).1 (cS D) (piB X (C.Q τ) (C.Qi τ) u' τ)
      (piB X (Qcs C τ) (Qics C τ) u' τ) (sigB X (C.Q τ) (C.Qi τ) τ) σc (sigC_eq C τ)
      (fun _ hh => piC_eq C u' τ hh) (C.muW u' τ) (muNB D 1) hμW'.2.2.1 x y]
    exact hbe' x (dd_sub C τ hyc hx) y (dd_sub C τ hyc hy)

  set γc := Formalism.L2.SG.RealObj.trG (Qcs C τ) (Qics C τ) (γ (vOf X τ)) with hγc
  have hom := Formalism.L2.SG.RealObj.EnergyIntOm.mem_om X (Formalism.L2.SG.Pf.cfS_ne D) (transpC' C τ) hsc u u' c hc γ hγ
  rw [zc_eq, zc_eq] at hom
  have hint := CompanionTheory.D.Upq.BesselFunctionalConstruction.ooConv CompanionTheory.Lime.BM.inputs D.R.k D.R.rS _ _ (Dc C one_pos u u' τ) (epsSH D.R) (lamD D τ) h _ σc w0
    _ _ νq νq' hS hS' l l' hl hl' γc hom

  set μGc := muGB X (Qcs C τ) (Qics C τ) τ with hμGc
  set F : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS → ℝ≥0∞ :=
    fun m => ‖l (σc (Matrix.of m) w0)‖ₑ * ‖l' (σc (γc⁻¹ * Matrix.of m) w0)‖ₑ with hF
  have hFfin : ∫⁻ m, F m ∂μGc < ⊤ := by
    have hfi := hint.2
    unfold HasFiniteIntegral at hfi
    refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun m => ?_)) hfi
    simp only [hF]
    rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _),
      ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, mul_comm]
  clear_value F μGc

  obtain ⟨hyiU, hyi⟩ := Formalism.MainNotions.S.Inh.unitary_group_inv_mem yc hyc
  set yi := Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * ycᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS with hyidef
  have hyi' : yc * yi = 1 := mul_eq_one_comm.mp hyi
  have hR : ∫⁻ m, F (Formalism.FourierDecayAlt.B.rmulF yi m) ∂μGc = ∫⁻ m, F m ∂μGc := by
    have hrm : μGc.map (Formalism.FourierDecayAlt.B.rmulF yi) = μGc := by
      rw [hμGc]
      exact (Formalism.L2.SG.Pf.BaseOf.haarG_B (n_eq' X) (X.B.I.ε (vOf X τ)) h2 hg).right yi hyiU
    rw [← rmulE_coe yi yc hyi hyi', ← lintegral_map_equiv F (rmulE yi yc hyi hyi'), rmulE_coe, hrm]

  have hTe : MeasurableEmbedding (fun x : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) =>
      (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (Qcs C τ) (Qics C τ) x) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) :=
    (Formalism.L2.SG.Pf.BaseOf.trG_closedEmb (n_eq' X) (X.B.I.ε (vOf X τ)) h2).measurableEmbedding
  have hCV : ∫⁻ x, F (Formalism.FourierDecayAlt.B.rmulF yi (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (Qcs C τ) (Qics C τ) x)))
      ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) = ∫⁻ m, F (Formalism.FourierDecayAlt.B.rmulF yi m) ∂μGc := by
    rw [hμGc]
    unfold muGB
    exact (hTe.lintegral_map (fun m => F (Formalism.FourierDecayAlt.B.rmulF yi m))).symm

  have key : ∀ x : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)),
      σc (Formalism.L2.SG.RealObj.trG (Qcs C τ) (Qics C τ) x * yi) w0 = X.B.σ (vOf X τ) (uMat x) (X.B.w (vOf X τ)) := by
    intro x
    have hTx := Formalism.L2.SG.Pf.LTL.trG_mem (Qcs C τ) (Qics C τ) _ h2 hg x
    rw [hw0, sigC_mul C τ (Formalism.MainNotions.S.Inh.mul_mem_UH_Hpk_nonempty_parameter_models _ _ hTx hyiU) hyc, Matrix.mul_assoc, hyi, Matrix.mul_one]
    show X.B.σ (vOf X τ) (Qcs C τ * (Qics C τ * uMat x * Qcs C τ) * Qics C τ) (X.B.w (vOf X τ)) = _
    congr 2
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one]
  have hγinv : γc⁻¹ = Qics C τ * uMat (γ (vOf X τ))⁻¹ * Qcs C τ := by
    refine Matrix.inv_eq_left_inv ?_
    rw [hγc]
    unfold Formalism.L2.SG.RealObj.trG
    calc Qics C τ * uMat (γ (vOf X τ))⁻¹ * Qcs C τ * (Qics C τ * uMat (γ (vOf X τ)) * Qcs C τ)
        = Qics C τ * (uMat (γ (vOf X τ))⁻¹ * (Qcs C τ * Qics C τ) * uMat (γ (vOf X τ))) * Qcs C τ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h2, Matrix.mul_one, uMat_inv_mul', Matrix.mul_one, h1]
  have hpt : ∀ x : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)),
      ‖X.Wloc u (vOf X τ) x‖ₑ * ‖X.Wloc u' (vOf X τ) ((γ (vOf X τ))⁻¹ * x)‖ₑ =
        (‖a‖ₑ * ‖a'‖ₑ) * F (Formalism.FourierDecayAlt.B.rmulF yi (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (Qcs C τ) (Qics C τ) x))) := by
    intro x
    have e2 : γc⁻¹ * Matrix.of (Formalism.FourierDecayAlt.B.rmulF yi (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (Qcs C τ) (Qics C τ) x))) =
        Formalism.L2.SG.RealObj.trG (Qcs C τ) (Qics C τ) ((γ (vOf X τ))⁻¹ * x) * yi := by
      show γc⁻¹ * (Formalism.L2.SG.RealObj.trG (Qcs C τ) (Qics C τ) x * yi) = _
      rw [hγinv]
      unfold Formalism.L2.SG.RealObj.trG
      rw [uMat_mul']
      calc Qics C τ * uMat (γ (vOf X τ))⁻¹ * Qcs C τ * (Qics C τ * uMat x * Qcs C τ * yi)
          = Qics C τ * uMat (γ (vOf X τ))⁻¹ * (Qcs C τ * Qics C τ) * uMat x * Qcs C τ * yi := by
            simp only [Matrix.mul_assoc]
        _ = Qics C τ * (uMat (γ (vOf X τ))⁻¹ * uMat x) * Qcs C τ * yi := by
            rw [h2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    rw [hW x, hW' ((γ (vOf X τ))⁻¹ * x), enorm_smul, enorm_smul, ← key x, ← key ((γ (vOf X τ))⁻¹ * x)]
    simp only [hF]
    rw [e2]
    show ‖a‖ₑ * ‖l (σc (Formalism.L2.SG.RealObj.trG (Qcs C τ) (Qics C τ) x * yi) w0)‖ₑ *
        (‖a'‖ₑ * ‖l' (σc (Formalism.L2.SG.RealObj.trG (Qcs C τ) (Qics C τ) ((γ (vOf X τ))⁻¹ * x) * yi) w0)‖ₑ) =
      ‖a‖ₑ * ‖a'‖ₑ * (‖l (σc (Formalism.L2.SG.RealObj.trG (Qcs C τ) (Qics C τ) x * yi) w0)‖ₑ *
        ‖l' (σc (Formalism.L2.SG.RealObj.trG (Qcs C τ) (Qics C τ) ((γ (vOf X τ))⁻¹ * x) * yi) w0)‖ₑ)
    ring
  calc ∫⁻ x, ‖X.Wloc u (vOf X τ) x‖ₑ * ‖X.Wloc u' (vOf X τ) ((γ (vOf X τ))⁻¹ * x)‖ₑ
        ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ)))
      = ∫⁻ x, (‖a‖ₑ * ‖a'‖ₑ) *
          F (Formalism.FourierDecayAlt.B.rmulF yi (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (Qcs C τ) (Qics C τ) x)))
          ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) := lintegral_congr hpt
    _ = (‖a‖ₑ * ‖a'‖ₑ) * ∫⁻ x,
          F (Formalism.FourierDecayAlt.B.rmulF yi (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (Qcs C τ) (Qics C τ) x)))
          ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) :=
        lintegral_const_mul' _ _ (ENNReal.mul_ne_top enorm_ne_top enorm_ne_top)
    _ < ⊤ := by
        rw [hCV, hR]
        exact ENNReal.mul_lt_top (ENNReal.mul_lt_top enorm_lt_top enorm_lt_top) hFfin

theorem stepIntG_of (hI : CompanionTheory.Lime.BM.Inputs2) (hRT : ReproTr) (hL2 : L2RightTranslation) (hGp : GapOfHyp)
    (hLF : ∀ (D : D7), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (X : HidaSetting D) (θ : ℝ) (C : Choice X θ), LocFactor C) :
    Formalism.L2.SG.RealObj.EnergyInt.StepIntG :=
  Formalism.L2.SG.RealObj.EnergyInt.stepIntG_of_loc (Formalism.L2.SG.RealObj.EnergyIntLoc.BM.locOrbG_of hI hRT hL2 hGp hLF)

end BM

end Formalism.L2.SG.RealObj.EnergyIntLoc
end
end

noncomputable section

open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice

open Formalism.L2.SG.RealObj.EnergyIntTor Formalism.L2.SG.RealObj.EnergyIntLoc Formalism.L2.SG.RealObj.EnergyIntOm Formalism.L2.SG.Pf.WuBL

open scoped InnerProductSpace ENNReal

namespace Formalism.L2.SG.RealObj.EnergyConvJ

namespace BM

variable {D : D7}

theorem weilPairJ (hI : CompanionTheory.Lime.BM.Inputs2) (hRT : ReproTr) (hL2 : L2RightTranslation) (hGp : GapOfHyp)
    (hLF : ∀ (D : D7), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (X : HidaSetting D) (θ : ℝ) (C : Choice X θ), LocFactor C)
    (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) (X : HidaSetting D) (τ : D.what₂.Tau) :
    ∃ (μS ν : D.what₂.Word → Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))),
      (∀ u, SFinite (μS u) ∧ SFinite (ν u) ∧
        (∀ f : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → ℝ≥0∞, Measurable f →
          ∫⁻ x, f x ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) = ∫⁻ x, ∫⁻ s, f (s * x) ∂(μS u) ∂(ν u)) ∧
        (μS u).map (fun x => x⁻¹) = μS u ∧ μS u (Formalism.L2.SG.Pf.WuDec.Sloc X u (vOf X τ))ᶜ = 0 ∧
        ∫⁻ z, ∫⁻ z', ∫⁻ s, ‖⟪X.B.σ (vOf X τ) (uMat z) (X.B.w (vOf X τ)),
            X.B.σ (vOf X τ) (uMat s) (X.B.σ (vOf X τ) (uMat z') (X.B.w (vOf X τ)))⟫_ℂ‖ₑ *
          ‖X.Wloc u (vOf X τ) z‖ₑ * ‖X.Wloc u (vOf X τ) z'‖ₑ ∂(μS u) ∂(ν u) ∂(ν u) < ⊤ ∧
        (∀ s ∈ Formalism.L2.SG.Pf.WuDec.Sloc X u (vOf X τ), (μS u).map (fun x => s * x) = μS u) ∧ μS u ≠ 0) ∧
      ∀ (u u' : D.what₂.Word) (sc : ℝ), 0 < sc → ∀ cv ∈ Formalism.L2.SG.RealObj.EnergyCut.GoodV (D := D) u u',
        ∀ g : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)),
          Zhat (X.B.I.ε (vOf X τ)) (frm X u sc (vOf X τ)) (frm X u' sc (vOf X τ)) (uMat g) = Matrix.diagonal cv →
          ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', ‖⟪X.B.σ (vOf X τ) (uMat z) (X.B.w (vOf X τ)),
              X.B.σ (vOf X τ) (uMat (s * g * s'⁻¹)) (X.B.σ (vOf X τ) (uMat z') (X.B.w (vOf X τ)))⟫_ℂ‖ₑ *
            ‖X.Wloc u (vOf X τ) z‖ₑ * ‖X.Wloc u' (vOf X τ) z'‖ₑ ∂(μS u') ∂(μS u) ∂(ν u') ∂(ν u) < ⊤ := by
  rcases isEmpty_or_nonempty D.what₂.Word with hEW | hNW
  · exact ⟨fun _ => 0, fun _ => 0, fun u => isEmptyElim u, fun u => isEmptyElim u⟩
  obtain ⟨C⟩ := Formalism.L2.SG.Pf.choiceExists X 1 one_pos
  have h1 := (transpC' C τ).1
  have h2 := (transpC' C τ).2.1
  have hg := (transpC' C τ).2.2.1
  obtain ⟨P, hP⟩ := Formalism.MainNotions.S.Inh.obj_cayleyU_rows D
  obtain ⟨yc, hyc, hycl⟩ := y_exists (n_eq' X) (X.B.I.ε (vOf X τ)) (epsSH D.R)
    (fun i => by rw [X.eps_eq]; exact congrArg (epsS D.R) (Fin.ext rfl))
    (X.B.lam (vOf X τ)) (lamD D τ)
    (fun i => by
      rw [X.lam_eq, show X.pl (vOf X τ) = τ from X.pl.apply_symm_apply τ]
      exact congrArg (lamS D.R (D.hc τ)) (Fin.ext rfl))
    (X.B.σ (vOf X τ)) (X.ds (vOf X τ)).2.2.1 (X.low (vOf X τ)).2 (Qcs C τ) (Qics C τ) h2 hg P hP
  set σc := sigB X (Qcs C τ) (Qics C τ) τ with hσc
  set w0 := σc yc (X.B.w (vOf X τ)) with hw0
  have hlow : IsLowUnitH D.R.k D.R.rS (epsSH D.R) (lamD D τ) σc w0 := by
    refine ⟨P, hP, ?_, hycl⟩
    rw [hw0, sigC_norm C τ hyc]
    exact (X.low (vOf X τ)).1
  obtain ⟨h, hgap, hok⟩ := hGp D hG τ
  set μNc := (muNB D 1).map (conjE (Formalism.L2.SG.Pf.muT_ne D)) with hμNc
  have hμN : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) μNc := muNc_haar one_pos
  have sN : SigmaFinite (muNB D 1) :=
    (Formalism.MainNotions.BridgeCSB.haarLieN _ _ _ (kapN_ne_zero D one_pos) (kapN_ne_top D 1)).1

  have hdat : ∀ u : D.what₂.Word, ∃ (l : X.B.H (vOf X τ) → X.Vloc u (vOf X τ)) (a : ℂ) (νq : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)),
      SFinite νq ∧
      Formalism.FourierDecayAlt.ThreeDimData.Side D.R.k D.R.rS (epsSH D.R) (lamD D τ) h σc w0 (zB X (C.Qi τ) u τ) Formalism.QuantumDeterminants.cStd
        (fun i => ((D.hcW u τ).u i : ℝ)) (piB X (Qcs C τ) (Qics C τ) u τ) (C.muW u τ) μNc
        (muGB X (Qcs C τ) (Qics C τ) τ) νq ∧
      (∀ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp σc w0, ∀ y ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp σc w0,
        Formalism.FourierDecayAlt.ThreeDimData.be (zB X (C.Qi τ) u τ) Formalism.QuantumDeterminants.cStd (piB X (Qcs C τ) (Qics C τ) u τ) σc (C.muW u τ) μNc x y =
          (innerSL ℂ (l y)).smulRight (l x)) ∧
      ∀ γ, X.Wloc u (vOf X τ) γ = a • l (X.B.σ (vOf X τ) (uMat γ) (X.B.w (vOf X τ))) := by
    intro u
    obtain ⟨l, a, hbe, hW⟩ := Formalism.L2.SG.RealObj.EnergyIntQ.BM.locDDQ hI hRT hL2 hGp hG C (hLF D hG X 1 C) u τ
    obtain ⟨νq, hsf, hS⟩ := sideC_SF C one_pos u τ hgap hok hlow
    have hμW := C.muW_haar u τ
    have : SigmaFinite (C.muW u τ) := hμW.1
    refine ⟨l, a, νq, hsf, hS, fun x hx y hy => ?_, hW⟩
    rw [← scale_eq D, be_tor (Formalism.L2.SG.Pf.muT_ne D) (zT C u τ).1 (cS D) (piB X (C.Q τ) (C.Qi τ) u τ)
      (piB X (Qcs C τ) (Qics C τ) u τ) (sigB X (C.Q τ) (C.Qi τ) τ) σc (sigC_eq C τ)
      (fun _ hh => piC_eq C u τ hh) (C.muW u τ) (muNB D 1) hμW.2.2.1 x y]
    exact hbe x (dd_sub C τ hyc hx) y (dd_sub C τ hyc hy)
  choose l a νq hsf hS hl hW using hdat

  obtain ⟨hyiU, hyi⟩ := Formalism.MainNotions.S.Inh.unitary_group_inv_mem yc hyc
  set yi := Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * ycᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS with hyidef
  have hyi' : yc * yi = 1 := mul_eq_one_comm.mp hyi
  set yJ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) :=
    Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.ujOf _ (inUJ_tr (transpC' C τ) hyiU) with hyJ
  have hTyJ : Matrix.of (Tm C τ yJ) = yi := by
    show Qics C τ * uMat yJ * Qcs C τ = yi
    rw [hyJ, Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.uMat_ujOf, show Qics C τ * (Qcs C τ * yi * Qics C τ) * Qcs C τ =
      (Qics C τ * Qcs C τ) * yi * (Qics C τ * Qcs C τ) by simp only [Matrix.mul_assoc], h1, Matrix.one_mul, Matrix.mul_one]
  have hTyJi : Matrix.of (Tm C τ yJ⁻¹) = yc := by
    rw [Tm_inv]
    show (Matrix.of (Tm C τ yJ))⁻¹ = yc
    rw [hTyJ]
    exact Matrix.inv_eq_right_inv hyi
  have key : ∀ x : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)), X.B.σ (vOf X τ) (uMat (x * yJ⁻¹)) (X.B.w (vOf X τ)) = σc (Matrix.of (Tm C τ x)) w0 := by
    intro x
    rw [← sigC_Tm C τ (x * yJ⁻¹), hw0, sigC_mul C τ (Tm_mem C τ x) hyc, Tm_mul]
    show σc (Matrix.of (Tm C τ x) * Matrix.of (Tm C τ yJ⁻¹)) (X.B.w (vOf X τ)) = _
    rw [hTyJi]
  have hWl : ∀ u (x : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))), X.Wloc u (vOf X τ) (x * yJ⁻¹) = a u • l u (σc (Matrix.of (Tm C τ x)) w0) := by
    intro u x
    rw [hW u, key]
  have hsig : ∀ y : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)), X.B.σ (vOf X τ) (uMat y) = σc (Matrix.of (Tm C τ y)) := fun y =>
    (sigC_Tm C τ y).symm

  have hμGc := haar_tr (n_eq' X) (X.B.I.ε (vOf X τ)) (Qcs C τ) (Qics C τ) h2 hg
  have hSH : ∀ u, Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Sset D.R.k D.R.rS (zB X (C.Qi τ) u τ))
      (Formalism.MainNotions.S.muS (C.muW u τ) μNc) := fun u =>
    isHaarOn_muS_gen (zT C u τ).1 (zT C u τ).2 (C.muW_haar u τ) (C.muW_one u τ)
      (Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.2 _ _ _ hμN)
  have hSc0 : ∀ u, Formalism.MainNotions.S.muS (C.muW u τ) μNc {m | Matrix.of m ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} = 0 := by
    intro u
    refine measure_mono_null ?_ (hSH u).2.2.1
    intro m hm
    simp only [Set.mem_ofPred_eq] at hm ⊢
    intro hmS
    apply hm
    obtain ⟨h0, hh0, n0, hn0, he⟩ := hmS
    rw [he]
    exact Formalism.MainNotions.S.Inh.mul_mem_UH_Hpk_nonempty_parameter_models _ _ hh0.1 hn0.1
  have hνc0 : ∀ u, νq u {m | Matrix.of m ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} = 0 := fun u =>
    quot_conc (hS u).2.2.2.2.2.2.2.2.2.2.2.2 hμGc.2.2.1 (hSc0 u) (hSH u).2.1
  have hcm : ∀ (c : ℝ≥0∞), c ≠ ⊤ → ∀ (μ : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))) (f : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → ℝ≥0∞),
      ∫⁻ x, c * f x ∂μ = c * ∫⁻ x, f x ∂μ := fun c hc μ f => lintegral_const_mul' c f hc
  refine ⟨fun u => (Formalism.MainNotions.S.muS (C.muW u τ) μNc).comap (Tm C τ),
    fun u => ((νq u).comap (Tm C τ)).map (MeasurableEquiv.mulRight yJ⁻¹), fun u => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · have := (hSH u).1
    have := sigmaFinite_comap C τ (hSc0 u)
    infer_instance
  · have := hsf u
    have := sFinite_comap C τ (μ := νq u)
    infer_instance
  · intro f hf
    have hf' : Measurable (fun y : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) => f (y * yJ⁻¹)) := hf.comp (measurable_mul_const _)
    have hq : Formalism.MainNotions.S.IsQuotMeas (muGB X (Qcs C τ) (Qics C τ) τ) (Formalism.MainNotions.S.muS (C.muW u τ) μNc) (νq u) :=
      (hS u).2.2.2.2.2.2.2.2.2.2.2.2
    rw [lintegral_map_equiv]
    calc ∫⁻ x, f x ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ)))
        = ∫⁻ x, f (x * yJ⁻¹) ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) := by
          rw [← lintegral_map hf (measurable_mul_const yJ⁻¹), Formalism.REAL.indefinite_unitary_unimodular _ _ yJ⁻¹]
      _ = _ := weil_J C τ hq (hSc0 u) (hνc0 u) _ hf'
      _ = _ := by
          refine lintegral_congr fun x => lintegral_congr fun s => ?_
          simp only [MeasurableEquiv.coe_mulRight, mul_assoc]
  · exact inv_comap C τ (hSc0 u) (muS_inv (zT C u τ).1 (zT C u τ).2
      (Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.1 _ _ _ _ (zT C u τ).1 (zT C u τ).2 (C.muW_haar u τ))
      (Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.2 _ _ _ hμN))
  · rw [(Tm_emb C τ).comap_apply]
    refine measure_mono_null ?_ (hSH u).2.2.1
    rintro _ ⟨x, hx, rfl⟩ hxs
    exact hx (sloc_of_sset C τ u x hxs)
  ·
    have hint := (CompanionTheory.D.Upq.BesselFunctionalConstruction.quadConv CompanionTheory.Lime.BM.inputs D.R.k D.R.rS _ _ (Dc C one_pos u u τ) (epsSH D.R) (lamD D τ) h _
      σc w0 _ _ (νq u) (νq u) (hS u) (hS u) (l u) (l u) (hl u) (hl u)).2
    have e : ∀ x x' s : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)),
        ‖⟪X.B.σ (vOf X τ) (uMat (x * yJ⁻¹)) (X.B.w (vOf X τ)), X.B.σ (vOf X τ) (uMat s) (X.B.σ (vOf X τ) (uMat (x' * yJ⁻¹)) (X.B.w (vOf X τ)))⟫_ℂ‖ₑ *
          ‖X.Wloc u (vOf X τ) (x * yJ⁻¹)‖ₑ * ‖X.Wloc u (vOf X τ) (x' * yJ⁻¹)‖ₑ =
        (‖a u‖ₑ * ‖a u‖ₑ) * (((‖⟪σc (Matrix.of (Tm C τ x)) w0, σc (Matrix.of (Tm C τ s))
          (σc (Matrix.of (Tm C τ x')) w0)⟫_ℂ‖₊ : NNReal) : ℝ≥0∞) * ((‖l u (σc (Matrix.of (Tm C τ x)) w0)‖₊ : NNReal) : ℝ≥0∞) *
          ((‖l u (σc (Matrix.of (Tm C τ x')) w0)‖₊ : NNReal) : ℝ≥0∞)) := by
      intro x x' s
      rw [key, key, hsig s, hWl, hWl, enorm_smul, enorm_smul]
      show _ * (‖a u‖ₑ * ‖l u (σc (Matrix.of (Tm C τ x)) w0)‖ₑ) * (‖a u‖ₑ * ‖l u (σc (Matrix.of (Tm C τ x')) w0)‖ₑ) = _
      simp only [eNorm_eq_nnNorm]
      ring
    have step : ∫⁻ z, ∫⁻ z', ∫⁻ s, ‖⟪X.B.σ (vOf X τ) (uMat z) (X.B.w (vOf X τ)), X.B.σ (vOf X τ) (uMat s)
        (X.B.σ (vOf X τ) (uMat z') (X.B.w (vOf X τ)))⟫_ℂ‖ₑ * ‖X.Wloc u (vOf X τ) z‖ₑ * ‖X.Wloc u (vOf X τ) z'‖ₑ
          ∂((Formalism.MainNotions.S.muS (C.muW u τ) μNc).comap (Tm C τ))
          ∂(((νq u).comap (Tm C τ)).map (MeasurableEquiv.mulRight yJ⁻¹))
          ∂(((νq u).comap (Tm C τ)).map (MeasurableEquiv.mulRight yJ⁻¹)) =
        (‖a u‖ₑ * ‖a u‖ₑ) * ∫⁻ x, ∫⁻ x', ∫⁻ s, (((‖⟪σc (Matrix.of (Tm C τ x)) w0, σc (Matrix.of (Tm C τ s))
          (σc (Matrix.of (Tm C τ x')) w0)⟫_ℂ‖₊ : NNReal) : ℝ≥0∞) * ((‖l u (σc (Matrix.of (Tm C τ x)) w0)‖₊ : NNReal) : ℝ≥0∞) *
          ((‖l u (σc (Matrix.of (Tm C τ x')) w0)‖₊ : NNReal) : ℝ≥0∞))
          ∂((Formalism.MainNotions.S.muS (C.muW u τ) μNc).comap (Tm C τ)) ∂((νq u).comap (Tm C τ)) ∂((νq u).comap (Tm C τ)) := by
      rw [lintegral_map_equiv, ← hcm _ (ENNReal.mul_ne_top enorm_ne_top enorm_ne_top)]
      refine lintegral_congr fun x => ?_
      rw [lintegral_map_equiv, ← hcm _ (ENNReal.mul_ne_top enorm_ne_top enorm_ne_top)]
      refine lintegral_congr fun x' => ?_
      rw [← hcm _ (ENNReal.mul_ne_top enorm_ne_top enorm_ne_top)]
      refine lintegral_congr fun s => ?_
      exact e x x' s
    rw [step]
    have hL := lintegral_three_comap C τ (hνc0 u) (hSc0 u) (fun m m' p => ((‖⟪σc (Matrix.of m) w0, σc (Matrix.of p)
          (σc (Matrix.of m') w0)⟫_ℂ‖₊ : NNReal) : ℝ≥0∞) * ((‖l u (σc (Matrix.of m) w0)‖₊ : NNReal) : ℝ≥0∞) *
          ((‖l u (σc (Matrix.of m') w0)‖₊ : NNReal) : ℝ≥0∞))
    beta_reduce at hL
    rw [hL]
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top enorm_lt_top enorm_lt_top) hint
  · intro s hs
    have hmap : ((Formalism.MainNotions.S.muS (C.muW u τ) μNc).comap (Tm C τ)).map (Tm C τ) = Formalism.MainNotions.S.muS (C.muW u τ) μNc := by
      rw [(Tm_emb C τ).map_comap, Measure.restrict_eq_self_of_ae_mem]
      rw [ae_iff]
      refine measure_mono_null (fun m hm => ?_) (hSc0 u)
      simp only [Set.mem_ofPred_eq] at hm ⊢
      exact fun h => hm (mem_range_Tm C τ h)
    have hTs := sset_of_sloc C τ u s hs
    have hleft := (hSH u).2.2.2 _ hTs
    have hlm : Measurable (Formalism.QuantumDeterminants.lmulM (k := D.R.k) (r := D.R.rS) (Matrix.of (Tm C τ s))) :=
      (Formalism.MainNotions.BridgeCSB.continuous_lmulM _).measurable
    have hcomm : Tm C τ ∘ (fun x => s * x) = Formalism.QuantumDeterminants.lmulM (Matrix.of (Tm C τ s)) ∘ Tm C τ := by
      funext y
      exact Tm_mul C τ s y
    rw [← (Tm_emb C τ).comap_map (((Formalism.MainNotions.S.muS (C.muW u τ) μNc).comap (Tm C τ)).map (fun x => s * x)),
      Measure.map_map (Tm_emb C τ).measurable (measurable_const_mul s), hcomm,
      ← Measure.map_map hlm (Tm_emb C τ).measurable, hmap, hleft]
  · intro h0
    beta_reduce at h0
    have hmap : ((Formalism.MainNotions.S.muS (C.muW u τ) μNc).comap (Tm C τ)).map (Tm C τ) = Formalism.MainNotions.S.muS (C.muW u τ) μNc := by
      rw [(Tm_emb C τ).map_comap, Measure.restrict_eq_self_of_ae_mem]
      rw [ae_iff]
      refine measure_mono_null (fun m hm => ?_) (hSc0 u)
      simp only [Set.mem_ofPred_eq] at hm ⊢
      exact fun h => hm (mem_range_Tm C τ h)
    apply (hSH u).2.1
    rw [← hmap, h0, Measure.map_zero]
  ·
    intro u u' sc hsc cv hcv g hgd
    have hom := mem_om_loc (Formalism.L2.SG.Pf.cfS_ne D) (transpC' C τ) hsc u u' cv hcv g hgd
    rw [zc_eq, zc_eq] at hom
    set γc := Formalism.L2.SG.RealObj.trG (Qcs C τ) (Qics C τ) g with hγc
    have hint := (CompanionTheory.D.Upq.BesselFunctionalConstruction.quadConv CompanionTheory.Lime.BM.inputs D.R.k D.R.rS _ _ (Dc C one_pos u u' τ) (epsSH D.R) (lamD D τ) h _
      σc w0 _ _ (νq u) (νq u') (hS u) (hS u') (l u) (l u') (hl u) (hl u')).1 γc hom
    have hsg : ∀ s s' : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)),
        X.B.σ (vOf X τ) (uMat (s * g * s'⁻¹)) = σc (Matrix.of (Tm C τ s) * γc * (Matrix.of (Tm C τ s'))⁻¹) := by
      intro s s'
      rw [hsig, Tm_mul, Tm_mul, Tm_inv]
      rfl
    have e : ∀ x x' s s' : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)),
        ‖⟪X.B.σ (vOf X τ) (uMat (x * yJ⁻¹)) (X.B.w (vOf X τ)), X.B.σ (vOf X τ) (uMat (s * g * s'⁻¹))
          (X.B.σ (vOf X τ) (uMat (x' * yJ⁻¹)) (X.B.w (vOf X τ)))⟫_ℂ‖ₑ * ‖X.Wloc u (vOf X τ) (x * yJ⁻¹)‖ₑ * ‖X.Wloc u' (vOf X τ) (x' * yJ⁻¹)‖ₑ =
        (‖a u‖ₑ * ‖a u'‖ₑ) * (((‖⟪σc (Matrix.of (Tm C τ x)) w0,
          σc (Matrix.of (Tm C τ s) * γc * (Matrix.of (Tm C τ s'))⁻¹) (σc (Matrix.of (Tm C τ x')) w0)⟫_ℂ‖₊ : NNReal) : ℝ≥0∞) *
          ((‖l u (σc (Matrix.of (Tm C τ x)) w0)‖₊ : NNReal) : ℝ≥0∞) *
          ((‖l u' (σc (Matrix.of (Tm C τ x')) w0)‖₊ : NNReal) : ℝ≥0∞)) := by
      intro x x' s s'
      rw [key, key, hsg, hWl, hWl, enorm_smul, enorm_smul]
      show _ * (‖a u‖ₑ * ‖l u (σc (Matrix.of (Tm C τ x)) w0)‖ₑ) * (‖a u'‖ₑ * ‖l u' (σc (Matrix.of (Tm C τ x')) w0)‖ₑ) = _
      simp only [eNorm_eq_nnNorm]
      ring
    have step : ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', ‖⟪X.B.σ (vOf X τ) (uMat z) (X.B.w (vOf X τ)),
        X.B.σ (vOf X τ) (uMat (s * g * s'⁻¹)) (X.B.σ (vOf X τ) (uMat z') (X.B.w (vOf X τ)))⟫_ℂ‖ₑ *
          ‖X.Wloc u (vOf X τ) z‖ₑ * ‖X.Wloc u' (vOf X τ) z'‖ₑ
          ∂((Formalism.MainNotions.S.muS (C.muW u' τ) μNc).comap (Tm C τ)) ∂((Formalism.MainNotions.S.muS (C.muW u τ) μNc).comap (Tm C τ))
          ∂(((νq u').comap (Tm C τ)).map (MeasurableEquiv.mulRight yJ⁻¹))
          ∂(((νq u).comap (Tm C τ)).map (MeasurableEquiv.mulRight yJ⁻¹)) =
        (‖a u‖ₑ * ‖a u'‖ₑ) * ∫⁻ x, ∫⁻ x', ∫⁻ s, ∫⁻ s', (((‖⟪σc (Matrix.of (Tm C τ x)) w0,
          σc (Matrix.of (Tm C τ s) * γc * (Matrix.of (Tm C τ s'))⁻¹) (σc (Matrix.of (Tm C τ x')) w0)⟫_ℂ‖₊ : NNReal) : ℝ≥0∞) *
          ((‖l u (σc (Matrix.of (Tm C τ x)) w0)‖₊ : NNReal) : ℝ≥0∞) *
          ((‖l u' (σc (Matrix.of (Tm C τ x')) w0)‖₊ : NNReal) : ℝ≥0∞))
          ∂((Formalism.MainNotions.S.muS (C.muW u' τ) μNc).comap (Tm C τ)) ∂((Formalism.MainNotions.S.muS (C.muW u τ) μNc).comap (Tm C τ))
          ∂((νq u').comap (Tm C τ)) ∂((νq u).comap (Tm C τ)) := by
      rw [lintegral_map_equiv, ← hcm _ (ENNReal.mul_ne_top enorm_ne_top enorm_ne_top)]
      refine lintegral_congr fun x => ?_
      rw [lintegral_map_equiv, ← hcm _ (ENNReal.mul_ne_top enorm_ne_top enorm_ne_top)]
      refine lintegral_congr fun x' => ?_
      rw [← hcm _ (ENNReal.mul_ne_top enorm_ne_top enorm_ne_top)]
      refine lintegral_congr fun s => ?_
      rw [← hcm _ (ENNReal.mul_ne_top enorm_ne_top enorm_ne_top)]
      refine lintegral_congr fun s' => ?_
      exact e x x' s s'
    rw [step]
    have hL := lintegral_four_comap C τ (hνc0 u) (hνc0 u') (hSc0 u) (hSc0 u') (fun m m' p p' => ((‖⟪σc (Matrix.of m) w0,
          σc (Matrix.of p * γc * (Matrix.of p')⁻¹) (σc (Matrix.of m') w0)⟫_ℂ‖₊ : NNReal) : ℝ≥0∞) *
          ((‖l u (σc (Matrix.of m) w0)‖₊ : NNReal) : ℝ≥0∞) * ((‖l u' (σc (Matrix.of m') w0)‖₊ : NNReal) : ℝ≥0∞))
    beta_reduce at hL
    rw [hL]
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top enorm_lt_top enorm_lt_top) hint

end BM

end Formalism.L2.SG.RealObj.EnergyConvJ
end
end

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

open scoped InnerProductSpace ENNReal

namespace Formalism.L2.SG.RealObj.EnergyFinal

namespace BM

theorem stepIntG_holds (hI : CompanionTheory.Lime.BM.Inputs2) : Formalism.L2.SG.RealObj.EnergyInt.StepIntG :=
  Formalism.L2.SG.RealObj.EnergyIntLoc.BM.stepIntG_of hI Formalism.L2.SG.Pf.WuBL.reproduction_translation Formalism.L2.SG.Pf.WuBL.l2RightTranslation_thm
    Formalism.L2.SG.Pf.WuBL.parameter_gap_of_hypothesis (fun _ hG _ _ C => Formalism.L2.SG.Pf.LocF.locFactor_holds hG C)

theorem weilPairJ_holds (hI : CompanionTheory.Lime.BM.Inputs2) {D : D7} (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D)
    (X : HidaSetting D) (τ : D.what₂.Tau) :
    ∃ (μS ν : D.what₂.Word → Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))),
      (∀ u, SFinite (μS u) ∧ SFinite (ν u) ∧
        (∀ f : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → ℝ≥0∞, Measurable f →
          ∫⁻ x, f x ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) = ∫⁻ x, ∫⁻ s, f (s * x) ∂(μS u) ∂(ν u)) ∧
        (μS u).map (fun x => x⁻¹) = μS u ∧ μS u (Formalism.L2.SG.Pf.WuDec.Sloc X u (vOf X τ))ᶜ = 0 ∧
        ∫⁻ z, ∫⁻ z', ∫⁻ s, ‖⟪X.B.σ (vOf X τ) (uMat z) (X.B.w (vOf X τ)),
            X.B.σ (vOf X τ) (uMat s) (X.B.σ (vOf X τ) (uMat z') (X.B.w (vOf X τ)))⟫_ℂ‖ₑ *
          ‖X.Wloc u (vOf X τ) z‖ₑ * ‖X.Wloc u (vOf X τ) z'‖ₑ ∂(μS u) ∂(ν u) ∂(ν u) < ⊤ ∧
        (∀ s ∈ Formalism.L2.SG.Pf.WuDec.Sloc X u (vOf X τ), (μS u).map (fun x => s * x) = μS u) ∧ μS u ≠ 0) ∧
      ∀ (u u' : D.what₂.Word) (sc : ℝ), 0 < sc → ∀ cv ∈ Formalism.L2.SG.RealObj.EnergyCut.GoodV (D := D) u u',
        ∀ g : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)),
          Formalism.L2.SG.RealObj.Zhat (X.B.I.ε (vOf X τ)) (Formalism.L2.SG.RealObj.frm X u sc (vOf X τ))
            (Formalism.L2.SG.RealObj.frm X u' sc (vOf X τ)) (uMat g) = Matrix.diagonal cv →
          ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', ‖⟪X.B.σ (vOf X τ) (uMat z) (X.B.w (vOf X τ)),
              X.B.σ (vOf X τ) (uMat (s * g * s'⁻¹)) (X.B.σ (vOf X τ) (uMat z') (X.B.w (vOf X τ)))⟫_ℂ‖ₑ *
            ‖X.Wloc u (vOf X τ) z‖ₑ * ‖X.Wloc u' (vOf X τ) z'‖ₑ ∂(μS u') ∂(μS u) ∂(ν u') ∂(ν u) < ⊤ :=
  Formalism.L2.SG.RealObj.EnergyConvJ.BM.weilPairJ hI Formalism.L2.SG.Pf.WuBL.reproduction_translation Formalism.L2.SG.Pf.WuBL.l2RightTranslation_thm
    Formalism.L2.SG.Pf.WuBL.parameter_gap_of_hypothesis (fun _ hG _ _ C => Formalism.L2.SG.Pf.LocF.locFactor_holds hG C) hG X τ

end BM

end Formalism.L2.SG.RealObj.EnergyFinal
end
end

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.S.Pv.ConvG

open scoped InnerProductSpace ENNReal

namespace Formalism.L2.SG.RealObj.EnergyConvJ

namespace BM


set_option maxHeartbeats 400000 in
theorem locQuadGG_G_holds (hI : CompanionTheory.Lime.BM.Inputs2) : LocQuadGG_G := by
  intro D hG X u u' sc hsc v cv hcv g hZ
  obtain ⟨τ, hτ⟩ : ∃ τ, vOf X τ = v := ⟨X.pl v, X.pl.symm_apply_apply v⟩
  subst hτ
  obtain ⟨μS, ν, hloc, h4⟩ := Formalism.L2.SG.RealObj.EnergyFinal.BM.weilPairJ_holds hI hG X τ
  obtain ⟨hs1, hn1, hW1, hi1, h01, -⟩ := hloc u
  obtain ⟨hs2, hn2, hW2, hi2, h02, -⟩ := hloc u'
  have hfin := h4 u u' sc hsc cv hcv g hZ
  have hU := Formalism.L2.S.Pv.SchurTens.unitRep_of_URepOn (X.ds (vOf X τ)).2.2.1
  rw [quad_eq_GG (μ := Formalism.REAL.muG (X.B.I.ε (vOf X τ))) (μS := μS u) (μS' := μS u') (ν := ν u) (ν' := ν u')
    (S := Formalism.L2.SG.Pf.WuDec.Sloc X u (vOf X τ)) (S' := Formalism.L2.SG.Pf.WuDec.Sloc X u' (vOf X τ)) hU
    (X.B.w (vOf X τ)) (X.Wloc_cont u (vOf X τ)) (X.Wloc_cont u' (vOf X τ)) hW1 hW2 hi1 hi2 h01 h02
    (fun a ha => Formalism.L2.SG.Pf.WuDec.inv_mem_Sloc X u (vOf X τ) ha)
    (fun a ha => Formalism.L2.SG.Pf.WuDec.inv_mem_Sloc X u' (vOf X τ) ha)
    (fun s hs x => Formalism.L2.SG.Pf.WuDec.norm_Wloc_inv X u (vOf X τ) hs x)
    (fun s hs x => Formalism.L2.SG.Pf.WuDec.norm_Wloc_inv X u' (vOf X τ) hs x) g] at hfin
  unfold PhiGG at hfin
  exact hfin

end BM

end Formalism.L2.SG.RealObj.EnergyConvJ
end
end

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.S.Pv.ConvG

open scoped InnerProductSpace ENNReal Pointwise

namespace Formalism.L2.SG.RealObj.EnergyConvJ

namespace BM

variable {D : D7}


set_option maxHeartbeats 800000 in
theorem locQuad1_G_holds (hI : CompanionTheory.Lime.BM.Inputs2) : LocQuad1_G := by
  intro D hG X w μSl νl C hQ v
  obtain ⟨τ, hτ⟩ : ∃ τ, vOf X τ = v := ⟨X.pl v, X.pl.symm_apply_apply v⟩
  subst hτ
  obtain ⟨μS, ν, hloc, -⟩ := Formalism.L2.SG.RealObj.EnergyFinal.BM.weilPairJ_holds hI hG X τ
  obtain ⟨sS, sν, hWe, hinv, h0, h3, hli, hne⟩ := hloc w
  obtain ⟨hC0, hCt, hlocl, -⟩ := hQ
  obtain ⟨⟨hsfl, hnel, hconcl, hlil⟩, hWl⟩ := hlocl (vOf X τ)

  have hU := Formalism.L2.S.Pv.SchurTens.unitRep_of_URepOn (X.ds (vOf X τ)).2.2.1
  have e1 := triple_lintegral_eq (μ := Formalism.REAL.muG (X.B.I.ε (vOf X τ))) (μS := μS w) (ν := ν w)
    (S := Formalism.L2.SG.Pf.WuDec.Sloc X w (vOf X τ)) hU (X.B.w (vOf X τ)) (X.Wloc_cont w (vOf X τ)) hWe h0
    (fun s hs x => Formalism.L2.SG.Pf.WuDec.norm_Wloc_inv X w (vOf X τ) hs x)
  beta_reduce at e1
  have hJ : ∫⁻ a, Kv X w (vOf X τ) a ∂(ν w) < ⊤ := by
    have e2 : ∫⁻ a, Kv X w (vOf X τ) a ∂(ν w) = ∫⁻ z, ‖X.Wloc w (vOf X τ) z‖ₑ *
        ∫⁻ y, ‖⟪X.B.σ (vOf X τ) (uMat z) (X.B.w (vOf X τ)), X.B.σ (vOf X τ) (uMat y) (X.B.w (vOf X τ))⟫_ℂ‖ₑ *
          ‖X.Wloc w (vOf X τ) y‖ₑ ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) ∂(ν w) := rfl
    rw [e2, ← e1]
    exact h3

  set S : Subgroup (Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :=
    Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.RI.SG (X.B.I.ε (vOf X τ)) (fun a => rv X.B.I (vOf X τ) (X.eR a))
      (rv X.B.I (vOf X τ) (X.zR w)) with hSdef
  have hSc : IsClosed (S : Set (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))) := Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.RI.SG_closed _ _ _
  have hSset : (S : Set (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))) = Formalism.L2.SG.Pf.WuDec.Sloc X w (vOf X τ) := rfl
  have hNHsub : ∀ x, x ∈ Formalism.L2.SG.Pf.WuDec.NHloc X w (vOf X τ) → x ∈ Formalism.L2.SG.Pf.WuDec.Sloc X w (vOf X τ) := by
    rintro x ⟨m, hm, h, hh, rfl⟩
    exact Formalism.L2.SG.Pf.WuDec.mul_mem_Sloc X w _ (Formalism.L2.SG.Pf.WuDec.Nloc_sub X w _ hm)
      (Formalism.L2.SG.Pf.WuDec.Hloc_sub X w _ hh)
  have hG0 : Formalism.REAL.muG (X.B.I.ε (vOf X τ)) ≠ 0 := NeZero.ne _
  have hfc : IsFiniteMeasureOnCompacts (μS w) := fin_of_weil _ (μS w) (ν w) hG0 hWe
  obtain ⟨c, hc0, hct, hceq⟩ := Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.HC.unique_sf S hSc (μS w) (μSl (vOf X τ)) hne
    (by rw [hSset]; exact h0) (fun s hs => hli s hs) hfc hnel hsfl
    (by
      rw [hSset]
      apply measure_mono_null (t := (Formalism.L2.SG.Pf.WuDec.NHloc X w (vOf X τ))ᶜ) _ hconcl
      intro x hx h'
      exact hx (hNHsub x h'))
    (fun s hs => hlil s (sloc_sub_NH X w _ hs))

  have hsub : MeasurableEmbedding (Subtype.val : S → Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :=
    MeasurableEmbedding.subtype_coe hSc.measurableSet
  obtain ⟨hli', hmap⟩ := Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.HC.comap_inv S hSc (μS w) (by rw [hSset]; exact h0)
    (fun s hs => hli s hs)
  set μS' : Measure S := (μS w).comap Subtype.val with hμS'
  have : LocallyCompactSpace S := hSc.locallyCompactSpace
  have : SecondCountableTopology S := TopologicalSpace.Subtype.secondCountableTopology _
  have : SigmaCompactSpace S := sigmaCompactSpace_of_locallyCompact_secondCountable
  have : IsFiniteMeasureOnCompacts μS' := ⟨fun K hK => by
    rw [hμS', hsub.comap_apply]
    exact (hK.image continuous_subtype_val).measure_lt_top⟩
  have hne' : μS' ≠ 0 := by
    intro h00
    apply hne
    rw [← hmap, h00, Measure.map_zero]
  have hinv2 : (μS w).map Inv.inv = μS w := hinv
  have e : μS'.inv.map Subtype.val = μS'.map Subtype.val := by
    rw [Measure.inv, Measure.map_map hsub.measurable measurable_inv,
      show (Subtype.val ∘ (Inv.inv : S → S)) = (Inv.inv : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → _) ∘ Subtype.val from rfl,
      ← Measure.map_map measurable_inv hsub.measurable, hmap, hinv2]
  have hinv' : μS'.inv = μS' := by
    rw [← hsub.comap_map μS'.inv, e, hsub.comap_map]
  have : μS'.IsInvInvariant := ⟨hinv'⟩
  have : μS'.IsMulRightInvariant := by
    have h := (inferInstance : μS'.inv.IsMulRightInvariant)
    rwa [hinv'] at h
  have : μS'.IsOpenPosMeasure := by
    obtain ⟨K, hK, hK0⟩ : ∃ K : Set S, IsCompact K ∧ μS' K ≠ 0 := by
      by_contra hc
      push Not at hc
      apply hne'
      have : μS' Set.univ = 0 := by
        rw [← iUnion_compactCovering S]
        exact measure_iUnion_null fun n => hc _ (isCompact_compactCovering S n)
      exact Measure.measure_univ_eq_zero.mp this
    exact isOpenPosMeasure_of_mulLeftInvariant_of_compact K hK hK0
  have hlint : ∀ (f : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → ℝ≥0∞) (x : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))),
      ∫⁻ s, f (s * x) ∂(μS w) = ∫⁻ s : S, f ((s : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) * x) ∂μS' := by
    intro f x
    conv_lhs => rw [← hmap]
    rw [hsub.lintegral_map]
  have hW1 : ∀ f : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → ℝ≥0∞, Measurable f →
      ∫⁻ x, f x ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) =
        ∫⁻ x, ∫⁻ s : S, f ((s : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) * x) ∂μS' ∂(ν w) := by
    intro f hf
    rw [hWe f hf]
    exact lintegral_congr fun x => hlint f x
  have hμl : μSl (vOf X τ) = c⁻¹ • μS w := by
    rw [hceq, smul_smul, ENNReal.inv_mul_cancel hc0 hct, one_smul]
  have hci : c⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hc0
  have hW2 : ∀ f : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → ℝ≥0∞, Measurable f →
      ∫⁻ x, f x ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) =
        ∫⁻ x, ∫⁻ s : S, f ((s : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) * x) ∂μS' ∂(c⁻¹ • νl (vOf X τ)) := by
    intro f hf
    rw [hWl f hf, lintegral_smul_measure, smul_eq_mul, ← lintegral_const_mul' _ _ hci]
    refine lintegral_congr fun x => ?_
    rw [hμl, lintegral_smul_measure, smul_eq_mul, hlint f x]
  have hKinv : ∀ (s : S) (x : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))),
      Kv X w (vOf X τ) ((s : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) * x) = Kv X w (vOf X τ) x := by
    intro s x
    obtain ⟨m, hm, h, hh, he⟩ := sloc_sub_NH X w _ s.2
    rw [he]
    exact Kv_inv X w (vOf X τ) m hm h hh x
  have hind := Formalism.L2.SG.Pf.QuotIndep.quotIndep (Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) S hSc μS'
    (Formalism.REAL.muG (X.B.I.ε (vOf X τ))) (ν w) (c⁻¹ • νl (vOf X τ)) hW1 hW2 (Kv X w (vOf X τ))
    (measurable_Kv X w (vOf X τ)) hKinv
  rw [lintegral_smul_measure, smul_eq_mul] at hind
  have hfinal : ∫⁻ a, Kv X w (vOf X τ) a ∂(νl (vOf X τ)) = c * ∫⁻ a, Kv X w (vOf X τ) a ∂(ν w) := by
    rw [hind, ← mul_assoc, ENNReal.mul_inv_cancel hc0 hct, one_mul]
  rw [hfinal]
  exact ENNReal.mul_lt_top (lt_of_le_of_ne le_top hct) hJ

theorem stepConvG_holds (hI : CompanionTheory.Lime.BM.Inputs2) : StepConvG :=
  stepConvG_of (Formalism.L2.SG.RealObj.EnergyConvJ.BM.locQuadGG_G_holds hI) (Formalism.L2.SG.RealObj.EnergyConvJ.BM.locQuad1_G_holds hI)

end BM

end Formalism.L2.SG.RealObj.EnergyConvJ
end
end

noncomputable section

namespace Formalism.L2.SG.RealObj.EnergyConvJ

namespace BM

theorem stepIntG_jsz (hJ : CompanionTheory.Lime.BM.UniqGap) : Formalism.L2.SG.RealObj.EnergyInt.StepIntG :=
  Formalism.L2.SG.RealObj.EnergyFinal.BM.stepIntG_holds (CompanionTheory.Lime.BM.inputs2_of hJ)

theorem stepConvG_jsz (hJ : CompanionTheory.Lime.BM.UniqGap) : Formalism.L2.S.Pv.ConvG.StepConvG :=
  Formalism.L2.SG.RealObj.EnergyConvJ.BM.stepConvG_holds (CompanionTheory.Lime.BM.inputs2_of hJ)

theorem realObj_inInfinityX_jsz (hJ : CompanionTheory.Lime.BM.UniqGap) {D : Formalism.BasicNotions.D7}
    (hg : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ)
    (hsc : 0 < sc) : Formalism.L2.SG.RealObj.InInfinityX X u u' sc :=
  Formalism.L2.SG.Pf.realObj_inInfinityX_ofG (Formalism.L2.SG.RealObj.EnergyConvJ.BM.stepIntG_jsz hJ) (Formalism.L2.SG.RealObj.EnergyConvJ.BM.stepConvG_jsz hJ) hg X u u' sc hsc

end BM

end Formalism.L2.SG.RealObj.EnergyConvJ
