module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainOntoCuspFormsOfInnerProduct
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawTransportRelationsOfFamilyLaws
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PolarizationPairDerivation
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamAllQOfAllTrue
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MiStar2AtRealisation

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.OntoAllOfPrintsAndHecke
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.ChainOnto
theorem ontoAll_of_hecke_alt : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → ∀ D : D7, OntoAll D :=
  fun hHC hCusp hDS hHCM hCW hHowe hWeil hSW hSWc hDoub hUnr D =>
    GlobalTheory.T.thetaLiftChain_onto_cuspForms_of_innerProduct hHC hCusp hDS hHCM hCW D
      (_root_.GlobalTheory.T.heckeForm_of_doubling hWeil hCusp hSW hSWc hDoub hUnr D)
      (GlobalTheory.T.thetaChainUpwardLift_heckeParam_transferred hCusp hHowe D (GlobalTheory.T.thetaChain_level_properties D))
end GlobalTheory.ChainOnto
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ontoAll_of_theta_doubling : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → ∀ D : D7, OntoAll D := by
  first | exact @_root_.GlobalTheory.ChainOnto.ontoAll_of_hecke_alt | exact _root_.GlobalTheory.ChainOnto.ontoAll_of_hecke_alt | (intros; apply _root_.GlobalTheory.ChainOnto.ontoAll_of_hecke_alt <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainTheoremFromPublishedResultsAltAltAltAlt
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MiStar2OfFamilies
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DescentEVMemLevel
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
namespace GlobalTheory.MiTop
theorem descent_eV_mem_level_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.BottomHypotheses W → _root_.GlobalTheory.MiS.LevelHypothesis W → (∀ t F, (_root_.GlobalTheory.MiS.packageCoefficientSpace W).Θ t ((_root_.GlobalTheory.MiS.packageCoefficientSpace W).jR t (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs t F)) ∈ (_root_.GlobalTheory.MiS.packageCoefficientSpace W).EEl true) := by
  intro D L hT Gi Gl Kc Yd cX ex W hB hLv t F
  obtain ⟨-, -, -, hC, -⟩ := hB.hyp
  obtain ⟨⟨s, hs⟩, hRZ, gE, hU, hG, h2, hl0, hl1⟩ := hLv
  have hK := RealDat3.kFormR_of (R := W.Q.Rl) (F := W.Q.F) hC.models
  have hJ := RealDat3.jIsoR_of (R := W.Q.Rl) (F := W.Q.F) hC.models
  have hDn := Formalism.IndefR.CxPass.descent_of_types hs hK hJ hRZ hU hG h2 hl0 hl1 true
  have hE := Formalism.IndefR.Links.EvTie.evTie_real ⟨s, hs⟩ W.Q.Rl W.Q.F
  have hV : (_root_.GlobalTheory.MiS.packageCoefficientSpace W).jR t (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs t F) ∈ (_root_.GlobalTheory.MiS.packageCoefficientSpace W).V0C W.Q.F.cv true t :=
    Submodule.subset_span ⟨_, hE.1 t F, rfl⟩
  exact hDn t (Submodule.mem_map_of_mem hV)
end GlobalTheory.MiTop
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JointOfFamAllQ
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RelOfLinks
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
namespace GlobalTheory.MiTop
theorem rel_of_links_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), ∀ u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (d : _root_.GlobalTheory.MiTop.BottomData W u), (∀ t, (f.t t).Is) → MainX f.t → _root_.GlobalTheory.MiTop.LinkVanishes f d → _root_.GlobalTheory.MiTop.LinkTailCondition f → _root_.GlobalTheory.MiTop.LinkDescends f → _root_.GlobalTheory.MiTop.LinkSurjective f → _root_.GlobalTheory.MiTop.LinkCommutes f → _root_.GlobalTheory.MiTop.FamilyRatioCondition f → _root_.GlobalTheory.MiTop.FamilyServedCondition W → ∃ (U : D.what₂.Mu u →ₗ[ℂ] D.what₂.Mu u) (r : ℝ) (c : W.P.T → ℂ), 0 < r ∧ (∀ φ, ‖U φ‖ = r * ‖φ‖) ∧ _root_.GlobalTheory.MiTop.UnitCoefficients W c ∧ d.Rel U c := by
  intro D L hT Gi Gl Kc Yd cX ex W u f d hIs hMain hZ hTail hDown hOnto hComm hRat hServ
  obtain ⟨a, ha⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  obtain ⟨n, hn⟩ : ∃ n, 2 * n + 2 = D.R.m := ⟨a - 1, by omega⟩
  have h : 2 * n + 2 * 0 + 2 = D.R.m := by omega
  have h₀ : 0 + 2 * n + 2 = D.R.m := by omega
  have hN : 2 * (n + 1) = D.R.m := by omega
  obtain ⟨S, r, s, hr, hS, hs, hcomm⟩ := hComm (n + 1) hN
  have hBot : ∀ t, (f.t t).cBot ≠ 0 := fun t =>
    Finset.prod_ne_zero_iff.mpr (fun j hj => (hIs t).cI j (Finset.mem_range.mp hj))
  have hTop : ∀ t, (f.t t).cTop (n + 1) ≠ 0 := fun t => (hRat (n + 1) hN t).1
  refine ⟨(S.symm : D.what₂.Mu u →ₗ[ℂ] D.what₂.Mu u), r⁻¹, fun t => (f.t t).cTop (n + 1) * s / (f.t t).cBot,
    inv_pos.mpr hr, ?_, ?_, ?_⟩
  · intro φ
    have e := hS (S.symm φ)
    simp only [LinearEquiv.apply_symm_apply] at e
    simp only [LinearEquiv.coe_coe]
    rw [e, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
  · refine ⟨fun t => div_ne_zero (mul_ne_zero (hTop t) hs) (hBot t), ?_⟩
    intro w k hk
    refine GlobalTheory.T.valuation_eq_zero_of_rootOfSUnitRatio D.what₂.LL D.what₂.embLL w (_root_.GlobalTheory.MiTop.qPrime_alt W (W.Q.Rl.mu w)) _ _ (hRat (n + 1) hN (W.Q.Rl.mu w)).2
      (fun p hp hb => hServ w p hp hb) k ?_
    rw [hk]
    have a1 := hTop (W.Q.Rl.mu w)
    have a2 := hTop W.P.A3.A.μ0
    have b1 := hBot (W.Q.Rl.mu w)
    have b2 := hBot W.P.A3.A.μ0
    field_simp
  · intro T hT0
    obtain ⟨G₀, hG₀⟩ := hOnto n h T hT0
    refine ⟨fun φ₀ => (f.t W.P.A3.A.μ0).cTop (n + 1) * (f.t W.P.A3.A.μ0).tail (2 * (n + 1)) hN
      ((f.t W.P.A3.A.μ0).up (n + 1) (_root_.GlobalTheory.MiTop.col0_alt f W.P.A3.A.μ0 (S.symm φ₀))) G₀ / (f.t W.P.A3.A.μ0).cBot, ?_⟩
    intro φ₀ φ t F F' hFF α α' hrel y v
    obtain ⟨G, hG1, hGd⟩ := hDown n h t F'
    let sB : Bool → W.P.T := fun b => Bool.rec t W.P.A3.A.μ0 b
    let xB : Bool → D.what₂.Mu u := fun b => Bool.rec (S.symm φ) (S.symm φ₀) b
    let aB : Bool → ℂ := fun b => Bool.rec (α' / (f.t t).cBot) (α / (f.t W.P.A3.A.μ0).cBot) b
    let FB : ∀ b, (f.t (sB b)).CT := fun b => Bool.rec (motive := fun b => (f.t (sB b)).CT) G G₀ b
    have key := hMain n h h₀ Bool sB aB (fun b => _root_.GlobalTheory.MiTop.col0_alt f (sB b) (xB b)) FB
      (fun b => ((hZ n h₀ (sB b) (xB b)).1))
    rw [Fintype.sum_bool] at key
    have top : aB true * (f.t (sB true)).cTop (n + 1) * (f.t (sB true)).tail (2 * (n + 1)) h
          ((f.t (sB true)).up (n + 1) (_root_.GlobalTheory.MiTop.col0_alt f (sB true) (xB true))) (FB true) +
        aB false * (f.t (sB false)).cTop (n + 1) * (f.t (sB false)).tail (2 * (n + 1)) h
          ((f.t (sB false)).up (n + 1) (_root_.GlobalTheory.MiTop.col0_alt f (sB false) (xB false))) (FB false) = 0 := by
      have e1 := hcomm t (S.symm φ) G
      rw [LinearEquiv.apply_symm_apply] at e1
      have e2 := hTail (n + 1) hN t φ F F' hFF G hG1
      change α / (f.t W.P.A3.A.μ0).cBot * (f.t W.P.A3.A.μ0).cTop (n + 1) * (f.t W.P.A3.A.μ0).tail (2 * (n + 1)) hN
          ((f.t W.P.A3.A.μ0).up (n + 1) (_root_.GlobalTheory.MiTop.col0_alt f W.P.A3.A.μ0 (S.symm φ₀))) G₀ +
        α' / (f.t t).cBot * (f.t t).cTop (n + 1) * (f.t t).tail (2 * (n + 1)) hN ((f.t t).up (n + 1) (_root_.GlobalTheory.MiTop.col0_alt f t (S.symm φ))) G = 0
      rw [e1, e2]
      beta_reduce at hrel
      linear_combination hrel
    have bot := key top y v
    rw [Fintype.sum_bool] at bot
    have z1 := (hZ n h₀ W.P.A3.A.μ0 (S.symm φ₀)).2
      ((f.t W.P.A3.A.μ0).dn (2 * n + 1) ((f.t W.P.A3.A.μ0).ioT (2 * n) h G₀)) y v
    have z2 := (hZ n h₀ t (S.symm φ)).2 ((f.t t).dn (2 * n + 1) ((f.t t).ioT (2 * n) h G)) y v
    change α / (f.t W.P.A3.A.μ0).cBot * (f.t W.P.A3.A.μ0).cBot * (f.t W.P.A3.A.μ0).per 0 n h₀ (_root_.GlobalTheory.MiTop.col0_alt f W.P.A3.A.μ0 (S.symm φ₀))
        ((f.t W.P.A3.A.μ0).dn (2 * n + 1) ((f.t W.P.A3.A.μ0).ioT (2 * n) h G₀)) y v +
      α' / (f.t t).cBot * (f.t t).cBot * (f.t t).per 0 n h₀ (_root_.GlobalTheory.MiTop.col0_alt f t (S.symm φ))
        ((f.t t).dn (2 * n + 1) ((f.t t).ioT (2 * n) h G)) y v = 0 at bot
    rw [z1, z2] at bot
    have d1 : ((f.t W.P.A3.A.μ0).dn (2 * n + 1) ((f.t W.P.A3.A.μ0).ioT (2 * n) h G₀)).1 = T := hG₀
    have d2 : ((f.t t).dn (2 * n + 1) ((f.t t).ioT (2 * n) h G)).1 = _root_.GlobalTheory.MiTop.rowFormOfTuple W t F' := hGd
    rw [d1, d2, div_mul_cancel₀ _ (hBot _), div_mul_cancel₀ _ (hBot _)] at bot
    simpa only [LinearEquiv.coe_coe] using bot
end GlobalTheory.MiTop
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JointOfFamAllQ
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
namespace GlobalTheory.MiTop
theorem joint_of_famAllQ_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraModules → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.FamilyAllConditions W → _root_.GlobalTheory.MiTop.FamilyServedCondition W → _root_.GlobalTheory.MiTop.JointCondition W := by
  intro hCusp hHC D L hT Gi Gl Kc Yd cX ex W hFam hServ
  obtain ⟨z, hz, hzc, hu⟩ := hFam
  refine ⟨z, hz, hzc, fun u => ?_⟩
  obtain ⟨f, d, hPin, hLaws, hZ, hTail, hDown, hOnto, hComm, hRat⟩ := hu u
  have hMain : MainX f.t := GlobalTheory.T.seesawTransportRelations_of_familyLaws hCusp hHC D _ _ f.t hLaws
  obtain ⟨U, r, c, hr, hU, hc, hRel⟩ :=
    _root_.GlobalTheory.MiTop.rel_of_links_alt W u f d hLaws.tup hMain hZ hTail hDown hOnto hComm hRat hServ
  exact ⟨d, U, r, c, hPin, hr, hU, hc, hRel⟩
end GlobalTheory.MiTop
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JointOfFamAllQStatement
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.joint_of_famAllQ_of_servedQ : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraModules → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.FamilyAllConditions W → _root_.GlobalTheory.MiTop.FamilyServedCondition W → _root_.GlobalTheory.MiTop.JointCondition W := by
  first | exact @_root_.GlobalTheory.MiTop.joint_of_famAllQ_alt | exact _root_.GlobalTheory.MiTop.joint_of_famAllQ_alt | (intros; apply _root_.GlobalTheory.MiTop.joint_of_famAllQ_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MiStar2OfFamilies
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
namespace GlobalTheory.MiTop
theorem miStar2_of_bot_lev_fam_served_puNZ : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraModules → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.BottomHypotheses W → _root_.GlobalTheory.MiS.LevelHypothesis W → _root_.GlobalTheory.MiTop.FamilyAllConditions W → _root_.GlobalTheory.MiTop.FamilyServedCondition W → PuNZ D → (_root_.GlobalTheory.MiS.packageCoefficientSpace W).MIstar2 (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs) W.Q.sEE := by
  intro hDS hCR hHC D L hT Gi Gl Kc Yd cX ex W hB hLv hFam hSv hPu
  exact _root_.GlobalTheory.T.joint_star_product_nonvanishing_alt hDS hCR W hB (_root_.GlobalTheory.MiTop.descent_eV_mem_level_alt W hB hLv) (_root_.GlobalTheory.T.joint_of_famAllQ_of_servedQ hCR hHC W hFam hSv) hPu
end GlobalTheory.MiTop
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MiStar2OfFamiliesStatement
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mi_star2_of_pu_nz : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraModules → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.BottomHypotheses W → _root_.GlobalTheory.MiS.LevelHypothesis W → _root_.GlobalTheory.MiTop.FamilyAllConditions W → _root_.GlobalTheory.MiTop.FamilyServedCondition W → PuNZ D → (_root_.GlobalTheory.MiS.packageCoefficientSpace W).MIstar2 (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs) W.Q.sEE := by
  first | exact @_root_.GlobalTheory.MiTop.miStar2_of_bot_lev_fam_served_puNZ | exact _root_.GlobalTheory.MiTop.miStar2_of_bot_lev_fam_served_puNZ | (intros; apply _root_.GlobalTheory.MiTop.miStar2_of_bot_lev_fam_served_puNZ <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ServedQOfBot
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
namespace GlobalTheory.MiTop
theorem servedQ_of_bot_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.BottomHypotheses W → _root_.Formalism.IndefR.IndefiniteRealisationRecursion W.Q → _root_.GlobalTheory.MiTop.FamilyServedCondition W := by
  intro D L hT Gi Gl Kc Yd cX ex W _ _
  exact _root_.GlobalTheory.MiTop.served' W
end GlobalTheory.MiTop
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
theorem miStar2_of_allTrue_alt_alt : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.StrongApproxSU → ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → 1 ≤ B.R.rS → PuNZ (I.rec7 l Z) → (_root_.GlobalTheory.MiS.packageCoefficientSpace W).MIstar2 (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs) W.Q.sEE := by
  intro hHCF hCusp hDSC hHCM hCW hHowe hWeil hWSF hSWC hDbl hUDG hDSCl hSA B X I l Z L hT Gi Gl Kc Yd cX ex W hA hr hPu
  have hOnto := _root_.GlobalTheory.T.ontoAll_of_theta_doubling hHCF hCusp hDSC hHCM hCW hHowe hWeil hWSF hSWC hDbl hUDG (I.rec7 l Z)
  have hFam : _root_.GlobalTheory.MiTop.FamilyAllConditions W := by apply _root_.GlobalTheory.T.true_geometry_family_row_data_alt <;> assumption
  have hS := _root_.GlobalTheory.MiTop.servedQ_of_bot_alt W hA.pk.bot hA.rc.some
  exact _root_.GlobalTheory.T.mi_star2_of_pu_nz hDSCl hCusp hHCM W hA.pk.bot hA.pk.lev hFam hS hPu
end GlobalTheory.Fam
end
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.main_theorem_from_published_results_alt_alt_alt_alt : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.StrongApproxSU → ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → 1 ≤ B.R.rS → PuNZ (I.rec7 l Z) → (_root_.GlobalTheory.MiS.packageCoefficientSpace W).MIstar2 (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs) W.Q.sEE := by
  first | exact @_root_.GlobalTheory.Fam.miStar2_of_allTrue_alt_alt | exact _root_.GlobalTheory.Fam.miStar2_of_allTrue_alt_alt | (intros; apply _root_.GlobalTheory.Fam.miStar2_of_allTrue_alt_alt <;> assumption)
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.MiS GlobalTheory.Fam GlobalTheory.MiTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
open GlobalTheory.MiTop
namespace GlobalTheory.Fam
theorem miAt_of_truePack_alt_alt : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.StrongApproxSU → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.TruePackAlt W → 1 ≤ D.R.rS → PuNZ D → _root_.GlobalTheory.Fam.RealPackageCondition W := by
  intro h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 D L hT Gi Gl Kc Yd cX ex W hW hR hP
  cases hW with
  | mk W hA =>
    exact _root_.GlobalTheory.T.main_theorem_from_published_results_alt_alt_alt_alt h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 W hA hR hP
end GlobalTheory.Fam
end
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.MiS GlobalTheory.Fam GlobalTheory.MiTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
open GlobalTheory.MiTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.main_theorem_from_published_results_alt_alt_alt_alt_alt : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.StrongApproxSU → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.TruePackAlt W → 1 ≤ D.R.rS → PuNZ D → _root_.GlobalTheory.Fam.RealPackageCondition W := by
  first | exact @_root_.GlobalTheory.Fam.miAt_of_truePack_alt_alt | exact _root_.GlobalTheory.Fam.miAt_of_truePack_alt_alt | (intros; apply _root_.GlobalTheory.Fam.miAt_of_truePack_alt_alt <;> assumption)
end
end
