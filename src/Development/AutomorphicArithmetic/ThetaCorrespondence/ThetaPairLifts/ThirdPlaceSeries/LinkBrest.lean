module

public import Formalism.LocalToGlobal.Divisibility.DivisibilityRemainder.NoColumnCase.LvlWire
public import Formalism.LocalToGlobal.Divisibility.DivisibilityRemainder.LinkedMeasures.SlopeId
public import Formalism.LocalToGlobal.Divisibility.DivisibilityRemainder.ValueBounds.SlopeMaxB
public import Formalism.LocalToGlobal.Divisibility.DivisibilityRemainder.AdmissibleClasses.LinkGCl
public import Formalism.LocalToGlobal.Divisibility.DivisibilityRemainder.SharpFunctions.FunTop
public import Formalism.LocalToGlobal.Divisibility.DivisibilityRemainder.RationalColumns.BuRationalOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.JoinSISel
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsAtPoint

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BrestFinalAll
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HefunFunTop
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HefunPointB
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
  Formalism.L2.RowDataTransport
namespace Formalism.L2.DIV.FunSharpTop
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}
theorem funSharp_pt_alt [_root_.NumberField.IsTotallyComplex D.what₂.LL] {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex}
    {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)}
    {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) {s : ℕ} (hOk : P.A3.fam3.Ok3 s) (hsep : P.A3.fam3.TypesSep3) (Cl CHl : ℝ)
    (hP : CovolumeOntoIsometryConditions Q.Rl (faceT P Dcf Spf Zscf) Q.sEE (hkCan P.A3) Cl CHl) (hI : PassIn3 Q.Rl (faceT P Dcf Spf Zscf) Cl CHl)
    (hR : DivRows3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs P.Zs P.S0 P.S1 ex.p0 P.C P.NuC P.I) (hkap : RowsHoldKap3 P)
    (hde0 : 0 ≤ (Zscf (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).Zs).de) (hde : (Zscf (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).Zs).de ≤ 1 / 3) :
    D.div.RR.muMax + meanE D (fun e => Real.log (Y.kapR e)) ≤
      (Zscf (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).Zs).x ^ CHl * (Zscf (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).Zs).b +
        14 * (Zscf (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).Zs).la := by
  have hZs : (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).Zs = P.Zs := Q.zs
  have hS1 : HEq (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core.cols.toIndefData P.S1 := Q.s1
  have hpass : (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core.cols.muMaxRR ≤
      (Zscf (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).Zs).x ^ CHl * (Zscf (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).Zs).b -
        meanLog (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core.base.κ + 14 * (Zscf (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).Zs).la :=
    ((_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core.extra.passage hde0 hde _ (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core.extra.fun0).1
  have hmu : D.div.RR.muMax = (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core.cols.muMaxRR :=
    (Formalism.MainNotions.DIV.HookProducts.FunSharp.muMax_tie D.div.RR _ _ P.I.eRR hR.sharpRR.lat hR.sharpRR.metric).symm.trans
      (muMax_heq hZs hS1).symm
  have hκ : meanE D (fun e => Real.log (Y.kapR e)) = meanLog (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core.base.κ := by
    rw [(_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core.extra.level.2.1]
    exact meanEmb_eq_meanLog _ _ (fun σ => by rw [hkap σ, kap_heq hZs hS1])
  rw [hmu, hκ]
  linarith
end Formalism.L2.DIV.FunSharpTop
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.Pk Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Cx Formalism.L2.Top3 Formalism.L2.Top4 Formalism.L2.RowDataTransport Formalism.L2.DIV.Arith4S
namespace Formalism.L2.DIV.FunSharpTop
variable {𝒜 : FamClass} {sel : _root_.Formalism.L2.TwistSelection 𝒜} {selS : _root_.Formalism.L2.Top4.SelectionSpectralCondition 𝒜 sel} {selP : _root_.Formalism.L2.Top4.BaseLevelTiedChoiceAlt 𝒜 sel} {selDH : _root_.Formalism.L2.Top3.SelectionDefiniteHeightCondition 𝒜 sel}
  {selC : _root_.Formalism.L2.Top4.ColumnChoiceCompatibleSelection 𝒜 sel selP} {selK : _root_.Formalism.L2.Top4.KernelSelection 𝒜 sel}
theorem funSharp_fam_alt [∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (i : Fm.Ix x), IsTotallyComplex (Fm.D x i).what₂.LL]
    (selI : _root_.Formalism.L2.Top4.IndefiniteRealisationChoice' 𝒜 sel selS selP selDH selC selK) (hPA : _root_.Formalism.L2.Top4.AllRealisationsPrimitive sel selI)
    (DefRows4 : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x) (C CH : ℝ), Prop)
    (OneMapRow : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x), Prop)
    (hR : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      DivRows3 (Fm.D x i) (selP Fm hc x hx h i).1.A3 (selP Fm hc x hx h i).1.P0 (selP Fm hc x hx h i).1.ψ0 (selP Fm hc x hx h i).1.Ps (selP Fm hc x hx h i).1.ψs (selP Fm hc x hx h i).1.Zs (selP Fm hc x hx h i).1.S0 (selP Fm hc x hx h i).1.S1 (Fm.ex x hx i).p0 (selP Fm hc x hx h i).1.C (selP Fm hc x hx h i).1.NuC (selP Fm hc x hx h i).1.I)
    {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (CH : ℝ) (hCsz : 0 ≤ Fm.Csz) (hDG : Formalism.MainNotions.DGamSize Fm)
    (hRows : _root_.Formalism.L2.Top4.RowsAtSelAlt sel selI DefRows4 OneMapRow Fm hc CH) (hOne : _root_.Formalism.L2.Top4.EventuallyAlongSelection sel Fm hc (OneMapRow Fm hc)) (hN : DIVinN Fm) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (_ : Fm.x1 < x) (i : Fm.Ix x),
      (Fm.D x i).div.RR.muMax + DV.meanE (Fm.D x i) (fun e => Real.log ((Fm.X x i).kapR e)) ≤
        (Fm.L x i).sc.x ^ (max CH 1 + 1) * (Fm.L x i).sc.b := by
  obtain ⟨Cd, x4, hFDG⟩ := hDG
  obtain ⟨C, hC, x1, hr⟩ := hRows
  obtain ⟨x2, ho⟩ := hOne
  refine ⟨max (max (max x1 x2) (max x4 (x0F eps Fm.Ct Fm.Cc CH (ceF C 0 (2 + 9 * max Cd 0) (c0F Fm.Csz Fm.Cc Fm.CYL Fm.Ct)))))
    (max (sel Fm hc).1 56), fun x hx0 hx i => ?_⟩
  have hx1 : x1 ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hx0
  have hx2 : x2 ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hx0
  have hx4 : x4 ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)) hx0
  have hx5 : x0F eps Fm.Ct Fm.Cc CH (ceF C 0 (2 + 9 * max Cd 0) (c0F Fm.Csz Fm.Cc Fm.CYL Fm.Ct)) ≤ x :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)) hx0
  have h : (sel Fm hc).1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx0
  have g56 : (56 : ℝ) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx0
  obtain ⟨ra, -⟩ := hr x hx h hx1 i
  obtain ⟨prows, hsep⟩ := hPA Fm hc x hx h i
  have hok1 := (selC Fm hc x hx h i).ok1
  have hP : CovolumeOntoIsometryConditions (selI Fm hc x hx h i).Rl (selI Fm hc x hx h i).F (selI Fm hc x hx h i).sEE (hkCan (selP Fm hc x hx h i).1.A3) C CH :=
    { toPrimRows3 := prows, w1 := ra.w1, covol := ra.covol, onto := ra.onto hN, lamLow := ra.lamLow (ho x hx h hx2 i),
      seeIso := ra.seeIso, miStar := ra.miStar, fun0 := ra.fun0 hN }
  have hS := Fm.sizes x hx i
  have hFD : FactDGam (Fm.D x i) (max Cd 0) := J.factDGam_mono (hFDG x hx4 i) (le_max_left _ _)
  have hDGp := _root_.Formalism.L2.DIV.Cons.gamma_size_of_sizeData_alt (selP Fm hc x hx h i).2 (_root_.Formalism.L2.Top4Wire2.finite_T_of_squareIntegrableColumns (selC Fm hc x hx h i))
    hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hS.2.2.2.2.2.1 (selDH Fm hc x hx h i).1.1 (selDH Fm hc x hx h i).1.2 (Fm.L x i).Nc (cloudConstant_nonneg (Fm.L x i))
    (max Cd 0) (le_max_right _ _) hFD
  have eCc : (Fm.L x i).Cc = Fm.Cc := Fm.Cc_eq x i
  have eCt : (Fm.L x i).Ct = Fm.Ct := Fm.Ct_eq x i
  have eCY : (Fm.params x hx i).CYL = Fm.CYL := Fm.params_CYL x hx i
  have hxL : x0F (Fm.L x i).sc.eps (Fm.L x i).Ct (Fm.L x i).Cc CH
      (ceF C 0 (2 + 9 * max Cd 0) (c0F Fm.Csz (Fm.L x i).Cc (Fm.params x hx i).CYL (Fm.L x i).Ct)) ≤ (Fm.L x i).sc.x := by
    rw [Fm.L_eps x i, eCt, eCc, eCY, Fm.L_x x i hx]
    exact hx5
  obtain ⟨lam0', Sw, C1, H, dg, hdg, hdvd, hA⟩ := arithClause_rec (Fm.L x i) (selDH Fm hc x hx h i).1.1 (selDH Fm hc x hx h i).1.2 hS (selDH Fm hc x hx h i).2.1 (selDH Fm hc x hx h i).2.2 (Fm.params x hx i) (Fm.ex x hx i).fdef
    (Fm.ex x hx i).kap_def (selP Fm hc x hx h i).1.A3 (selP Fm hc x hx h i).1.tied.div.grp.card (selP Fm hc x hx h i).1.P0 (selP Fm hc x hx h i).1.ψ0 (selP Fm hc x hx h i).1.Ps (selP Fm hc x hx h i).1.ψs (selC Fm hc x hx h i).c.face (selC Fm hc x hx h i).Sp _ C CH Fm.Csz 0
    (2 + 9 * max Cd 0) (_root_.Formalism.L2.Top4Wire2.finite_T_of_squareIntegrableColumns (selC Fm hc x hx h i)) hDGp hC hCsz hxL (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm hc x hx h i) hok1 hsep C CH hP ra.pass)
  obtain ⟨Qq, hq0, hq1, hq2, -⟩ := (hA (Fm.D x i).u₀).q
  have key := _root_.Formalism.L2.DIV.FunSharpTop.funSharp_pt_alt (selI Fm hc x hx h i) hok1 hsep C CH hP ra.pass (hR Fm hc x hx h i) ra.kap hq0
    (third_of _ _ hq0 hq1 hq2)
  have hla : Formalism.BasicNotions.lam0 (Fm.D x i) = Real.log (Fintype.card (selP Fm hc x hx h i).1.Gp) := by
    unfold Formalism.BasicNotions.lam0
    rw [(selP Fm hc x hx h i).1.tied.div.grp.card]
  have key' : (Fm.D x i).div.RR.muMax + DV.meanE (Fm.D x i) (fun e => Real.log ((Fm.X x i).kapR e)) ≤
      (Fm.L x i).sc.x ^ CH * (Fm.L x i).sc.b + 14 * Formalism.BasicNotions.lam0 (Fm.D x i) := by
    rw [hla]
    exact key
  have hB1 : 1 ≤ (Fm.L x i).sc.b := by
    unfold Scale.b
    exact Real.one_le_exp (by unfold Scale.L; exact Real.rpow_nonneg (by linarith [(Fm.L x i).sc.one_lt_alt]) _)
  refine key'.trans (pow_absorb _ _ _ CH ?_ hB1 (Formalism.MainNotions.DIV.HookProducts.FunSharp.lambda_zero_le_four_b (Fm.L x i) hS))
  rw [Fm.L_x x i hx]
  exact g56
theorem closed_funSharp_alt (𝒜 : FamClass)
    (sel : _root_.Formalism.L2.TwistSelection 𝒜)
    (selS : _root_.Formalism.L2.Top4.SelectionSpectralCondition 𝒜 sel)
    (selP : _root_.Formalism.L2.Top4.BaseLevelTiedChoiceAlt 𝒜 sel)
    (selDH : _root_.Formalism.L2.Top3.SelectionDefiniteHeightCondition 𝒜 sel)
    (selC : _root_.Formalism.L2.Top4.ColumnChoiceCompatibleSelection 𝒜 sel selP)
    (selB : _root_.Formalism.L2.Top4.SelectionBundle 𝒜 sel selS selP selDH selC)
    (hRB : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      _root_.Formalism.IndefR.IndefiniteRealisationBoundedRows (selB Fm hc x hx h i))
    (hPA : _root_.Formalism.L2.Top4.AllRealisationsPrimitive sel (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB))
    (hDivG : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.DIV.DivRows3G (selP Fm hc x hx h i).1)
    (rRows : Closed (D3 3 𝒜) fun Fm CH => ∀ hc : D3 3 𝒜 Fm, _root_.Formalism.L2.Top4.RowsAtSelAlt sel (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) (fun Fm hc x hx h i C CH => _root_.Formalism.L2.Top4Wire2.DefRowsFAlt (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) Fm hc x hx h i C CH) (_root_.Formalism.L2.Top4.SingleMapCondition selB)
        Fm (d3_a hc) CH) :
    ∃ CF0 : ℝ → List ℝ → ℝ, Closed (D3 3 𝒜) fun {eps} Fm _ => ∀ _ : D3 3 𝒜 Fm, TuSize Fm → Formalism.MainNotions.DGamSize Fm → DIVinN Fm →
      ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (_ : Fm.x1 < x) (i : Fm.Ix x),
      (Fm.D x i).div.RR.muMax + DV.meanE (Fm.D x i) (fun e => Real.log ((Fm.X x i).kapR e)) ≤
        (Fm.L x i).sc.x ^ CF0 eps Fm.cOut * (Fm.L x i).sc.b := by
  have : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (i : Fm.Ix x), NumberField.IsTotallyComplex (Fm.D x i).what₂.LL :=
    fun Fm x i => (Fm.D x i).tcLL
  have hDivR : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.DIV.DivRows3 (Fm.D x i) (selP Fm hc x hx h i).1.A3 (selP Fm hc x hx h i).1.P0 (selP Fm hc x hx h i).1.ψ0 (selP Fm hc x hx h i).1.Ps
        (selP Fm hc x hx h i).1.ψs (selP Fm hc x hx h i).1.Zs (selP Fm hc x hx h i).1.S0 (selP Fm hc x hx h i).1.S1 (Fm.ex x hx i).p0 (selP Fm hc x hx h i).1.C (selP Fm hc x hx h i).1.NuC (selP Fm hc x hx h i).1.I :=
    fun Fm hc x hx h i => (hDivG Fm hc x hx h i).toRows (_root_.Formalism.IndefR.LevelRealisationRankEquality.tup_all_used_of_realisation (selB Fm hc x hx h i).Q)
  have hCsz : Closed (D3 3 𝒜) fun Fm _ => 0 ≤ Fm.Csz := Formalism.MainNotions.DIV.closed_Csz_ge_fn (D3 3 𝒜) fun _ => 0
  obtain ⟨f, hf⟩ := closed_atMid (rRows.and hCsz)
  refine ⟨fun e l => max (f e l) 1 + 1, hf.imp fun Fm _ _ hh hc _ hD hN => ?_⟩
  exact _root_.Formalism.L2.DIV.FunSharpTop.funSharp_fam_alt (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) hPA _ (_root_.Formalism.L2.Top4.SingleMapCondition selB) hDivR Fm (d3_a hc) _ hh.2 hD (hh.1 hc)
    ⟨0, fun x hx h _ i j => (hRB Fm (d3_a hc) x hx h i).oneMap j⟩ hN
theorem closed_funSharp_thr_alt (𝒜 : FamClass)
    (sel : _root_.Formalism.L2.TwistSelection 𝒜)
    (selS : _root_.Formalism.L2.Top4.SelectionSpectralCondition 𝒜 sel)
    (selP : _root_.Formalism.L2.Top4.BaseLevelTiedChoiceAlt 𝒜 sel)
    (selDH : _root_.Formalism.L2.Top3.SelectionDefiniteHeightCondition 𝒜 sel)
    (selC : _root_.Formalism.L2.Top4.ColumnChoiceCompatibleSelection 𝒜 sel selP)
    (selB : _root_.Formalism.L2.Top4.SelectionBundle 𝒜 sel selS selP selDH selC)
    (hRB : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      _root_.Formalism.IndefR.IndefiniteRealisationBoundedRows (selB Fm hc x hx h i))
    (hPA : _root_.Formalism.L2.Top4.AllRealisationsPrimitive sel (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB))
    (hDivG : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.DIV.DivRows3G (selP Fm hc x hx h i).1)
    (rRows : Closed (D3 3 𝒜) fun Fm CH => ∀ hc : D3 3 𝒜 Fm, _root_.Formalism.L2.Top4.RowsAtSelAlt sel (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) (fun Fm hc x hx h i C CH => _root_.Formalism.L2.Top4Wire2.DefRowsFAlt (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) Fm hc x hx h i C CH) (_root_.Formalism.L2.Top4.SingleMapCondition selB)
        Fm (d3_a hc) CH)
    (Eb Ec : List ℝ → ℝ) :
    Closed (D3 3 𝒜) fun Fm CH => ∀ _ : D3 3 𝒜 Fm, TuSize Fm → Formalism.MainNotions.DGamSize Fm →
      ∃ CF0 : List ℝ → ℝ, Fm.Large (Formalism.MainNotions.DIV.Proofs.thrHH Eb Ec CF0) CH ∧ (DIVinN Fm →
      ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (_ : Fm.x1 < x) (i : Fm.Ix x),
      (Fm.D x i).div.RR.muMax + DV.meanE (Fm.D x i) (fun e => Real.log ((Fm.X x i).kapR e)) ≤
        (Fm.L x i).sc.x ^ CF0 Fm.cOut * (Fm.L x i).sc.b) := by
  obtain ⟨CF0, h⟩ := _root_.Formalism.L2.DIV.FunSharpTop.closed_funSharp_alt 𝒜 sel selS selP selDH selC selB hRB hPA hDivG rRows
  exact closed_largeE (fun e => Formalism.MainNotions.DIV.Proofs.thrHH Eb Ec (CF0 e)) h
    fun {eps} Fm CH hL hP hc hT hD => ⟨CF0 eps, hL, hP hc hT hD⟩
end Formalism.L2.DIV.FunSharpTop
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BurrbPlug
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BurrbColFacts
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
namespace Formalism.L2.DIV.RatFullPt
section CSD
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) {G : Type} [Group G] [Fintype G]
  (r : Representation K G S.Forms) (X : Finset (G → K)) (P : Subgroup G) (ψ : P →* Kˣ)
end CSD
section Forms
variable {K : Type} [Field K] [NumberField K] [StarRing K]
end Forms
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
theorem indefinite_realisation_column_facts (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) {s : ℕ} (hOk : P.A3.fam3.Ok3 s) (hsep : P.A3.fam3.TypesSep3)
    (hP : PrimRows3 Q.Rl Q.F) (hS : (Q.Rl.toCx3 Q.F).SEEIso Q.sEE)
    (hM : (Q.Rl.toCx3 Q.F).MIstar2 (Q.F.eV (Q.Rl.toCx3 Q.F).zs) Q.sEE) : ColFacts P.S1 P.C := by
  have hC := complex_data_conditions_base_level_of_primitive_links hOk hsep Q.charW hP
  have hcols := (Q.Rl.toCx3 Q.F).exists_zeta_pairing_factors_through_periods Q.F.cr Q.F.cv (Q.F.eV (Q.Rl.toCx3 Q.F).zs) Q.sEE (hC.wf true) hC.h4pos (hC.what₂ true).1
    (hC.ratMu true) hC.jIsoR (hC.levs true).1 (hC.levs true).2.1 (hC.levs true).2.2 (definite_coordinates_in_good_part _ true)
    (EvTie.evTie_of_ok hOk Q.F _) hS hM
  have hDc : HEq (Dcf (Q.Rl.toCx3 Q.F).zs) P.Dc :=
    (congr_arg_heq Dcf Q.zs).trans (heq_of_eq Q.dc)
  have hSp : HEq (Spf (Q.Rl.toCx3 Q.F).zs) P.Sp := (congr_arg_heq Spf Q.zs).trans Q.sp
  exact colFacts_transport Q.zs hDc hSp Q.s1 Q.col
    ⟨hC.wf true, hC.h0, fun t => (Q.Rl.toCx3 Q.F).rowMat_bij Q.F.cr true (hC.what₂ true).1 (hC.ratMu true) t,
      (Classical.epsilon_spec hcols).1⟩
end Formalism.L2.DIV.RatFullPt
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT
namespace Formalism.L2.DIV.RatFullFam
open Formalism.L2.Top3 Formalism.L2.Top4
theorem buRat_rrFull_closed_alt (𝒜 : FamClass)
    (sel : _root_.Formalism.L2.TwistSelection 𝒜)
    (selS : _root_.Formalism.L2.Top4.SelectionSpectralCondition 𝒜 sel)
    (selP : _root_.Formalism.L2.Top4.BaseLevelTiedChoiceAlt 𝒜 sel)
    (selDH : _root_.Formalism.L2.Top3.SelectionDefiniteHeightCondition 𝒜 sel)
    (selC : _root_.Formalism.L2.Top4.ColumnChoiceCompatibleSelection 𝒜 sel selP)
    (selB : _root_.Formalism.L2.Top4.SelectionBundle 𝒜 sel selS selP selDH selC)
    (hPA : _root_.Formalism.L2.Top4.AllRealisationsPrimitive sel (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB))
    (hDivG : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.DIV.DivRows3G (selP Fm hc x hx h i).1)
    (hDcPtG : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.DIV.DcPtG (selP Fm hc x hx h i).1)
    (rRows : Closed (D3 3 𝒜) fun Fm CH => ∀ hc : D3 3 𝒜 Fm, _root_.Formalism.L2.Top4.RowsAtSelAlt sel (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) (fun Fm hc x hx h i C CH => _root_.Formalism.L2.Top4Wire2.DefRowsFAlt (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) Fm hc x hx h i C CH) (_root_.Formalism.L2.Top4.SingleMapCondition selB)
        Fm (d3_a hc) CH) :
    Closed (D3 3 𝒜) fun Fm _ => ∀ _ : D3 3 𝒜 Fm, TuSize Fm → Formalism.MainNotions.DGamSize Fm →
      (∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, (Fm.D x i).BuRational) ∧
        (∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, (Fm.D x i).RRFull) :=
  rRows.imp fun Fm CH _ h hc _ _ => by
    obtain ⟨C, _, x0, H⟩ := h hc
    have key : ∀ x ≥ max (max x0 (sel Fm (d3_a hc)).1) (Fm.x1 + 1), ∀ i : Fm.Ix x,
        (Fm.D x i).BuRational ∧ (Fm.D x i).RRFull := by
      intro x hx0 i
      have h0 : x0 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx0
      have hs : (sel Fm (d3_a hc)).1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx0
      have hx : Fm.x1 < x := lt_of_lt_of_le (by linarith) (le_trans (le_max_right _ _) hx0)
      obtain ⟨ra, _⟩ := H x hx hs h0 i
      obtain ⟨prows, hsep⟩ := hPA Fm (d3_a hc) x hx hs i
      have hok1 := (selC Fm (d3_a hc) x hx hs i).ok1
      have hU := _root_.Formalism.IndefR.LevelRealisationRankEquality.tup_all_used_of_realisation (selB Fm (d3_a hc) x hx hs i).Q
      have hR := (hDivG Fm (d3_a hc) x hx hs i).toRows hU
      have hPt := Formalism.L2.DIV.dcPt_of_G hU (hDcPtG Fm (d3_a hc) x hx hs i)
      have hF := _root_.Formalism.L2.DIV.RatFullPt.indefinite_realisation_column_facts ((_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) Fm (d3_a hc) x hx hs i) hok1 hsep prows ra.seeIso ra.miStar
      exact ⟨Formalism.L2.DIV.RatFullPt.buRational_of _ hok1 hF hR hPt (Fm.ties x i).bu_def,
        Formalism.L2.DIV.RatFullPt.rrFull_of _ hok1 hF hR⟩
    exact ⟨⟨_, fun x hx i => (key x hx i).1⟩, ⟨_, fun x hx i => (key x hx i).2⟩⟩
end Formalism.L2.DIV.RatFullFam
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkgLinkGCl
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace Formalism.L2.DIV.LinkGCl
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.L2.Top3
variable {eps : ℝ}
theorem gTiedF_of_sel_alt (Fm : FamP eps) (s : _root_.Formalism.L2.TwistSelectionFunctions Fm) : Formalism.L2.G.GroupCompatibilityFamily Fm :=
  _root_.Formalism.L2.gTiedF_of_C2S_alt Fm (_root_.Formalism.L2.Top3.tied_families_of_choice_alt s)
theorem closed_linkG (𝒜 : FamClass) (sel : _root_.Formalism.L2.TwistSelection 𝒜) : Closed (D3 3 𝒜) fun Fm _ => LinkG Fm :=
  Formalism.L2.G.linkG_concrete5 (D3 3 𝒜)
    (Closed.of_class fun Fm _ hc => _root_.Formalism.L2.DIV.LinkGCl.gTiedF_of_sel_alt Fm (sel Fm (d3_a hc)))
    (Closed.of_class fun Fm _ hc => admissible_tops_of_class Fm hc)
theorem closed_linkG_of_tuSize_dGamSize (𝒜 : FamClass) (sel : _root_.Formalism.L2.TwistSelection 𝒜) :
    Closed (D3 3 𝒜) fun Fm _ => ∀ _ : D3 3 𝒜 Fm, Formalism.MainNotions.TuSize Fm → Formalism.MainNotions.DGamSize Fm → LinkG Fm :=
  (_root_.Formalism.L2.DIV.LinkGCl.closed_linkG 𝒜 sel).imp fun _ _ _ h _ _ _ => h
end Formalism.L2.DIV.LinkGCl
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HbmuSlopeMaxB
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace Formalism.L2.DIV.SlopeMaxB
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.DIV.Proofs Formalism.MainNotions.DIV.Proofs.HHParts
theorem colTies_of_sel_alt {eps : ℝ} {Fm : FamP eps} (s : _root_.Formalism.L2.TwistSelectionFunctions Fm) : RT.tCVTies Fm := by
  obtain ⟨b, hs⟩ := stabF Fm
  refine ⟨max (max s.1 b) (Fm.x1 + 1), fun x hx i => ?_⟩
  have h1 : Fm.x1 < x := by have := le_trans (le_max_right _ _) hx; linarith
  have h0 : s.1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hb : b ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  exact ⟨⟨(s.2 x h1 h0 i).T.cols⟩, hs x hb h1 i⟩
theorem eventually_muMax_le_pow_ebMu_mul_of_tuSize {eps : ℝ} {Fm : FamP eps} (s : _root_.Formalism.L2.TwistSelectionFunctions Fm) (hT : TuSize Fm) :
    ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ (i : Fm.Ix x) u,
      (((Fm.D x i).fm u).lat 0).muMax ≤ (Fm.L x i).sc.x ^ EbMu Fm.cOut * (Fm.L x i).sc.b :=
  boundB_of_values Fm hT (tCV_of_ties Fm (_root_.Formalism.L2.DIV.SlopeMaxB.colTies_of_sel_alt s))
end Formalism.L2.DIV.SlopeMaxB
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.Pk Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Cx Formalism.L2.Top3 Formalism.L2.Top4 Formalism.L2.RowDataTransport Formalism.L2.DIV.Arith4S
namespace Formalism.L2.DIV.RestAll
theorem bRest_all_alt (𝒜 : FamClass) (Cabs : ℝ)
    (sel : _root_.Formalism.L2.TwistSelection 𝒜)
    (selS : _root_.Formalism.L2.Top4.SelectionSpectralCondition 𝒜 sel)
    (selP : _root_.Formalism.L2.Top4.BaseLevelTiedChoiceAlt 𝒜 sel)
    (selDH : _root_.Formalism.L2.Top3.SelectionDefiniteHeightCondition 𝒜 sel)
    (selC : _root_.Formalism.L2.Top4.ColumnChoiceCompatibleSelection 𝒜 sel selP)
    (selB : _root_.Formalism.L2.Top4.SelectionBundle 𝒜 sel selS selP selDH selC)
    (hRB : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      _root_.Formalism.IndefR.IndefiniteRealisationBoundedRows (selB Fm hc x hx h i))
    (hPA : _root_.Formalism.L2.Top4.AllRealisationsPrimitive sel (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB))
    (hDivG : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.DIV.DivRows3G (selP Fm hc x hx h i).1)
    (hDcPtG : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.DIV.DcPtG (selP Fm hc x hx h i).1)
    (rRows : Closed (D3 3 𝒜) fun Fm CH => ∀ hc : D3 3 𝒜 Fm, _root_.Formalism.L2.Top4.RowsAtSelAlt sel (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) (fun Fm hc x hx h i C CH => _root_.Formalism.L2.Top4Wire2.DefRowsFAlt (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) Fm hc x hx h i C CH) (_root_.Formalism.L2.Top4.SingleMapCondition selB)
        Fm (d3_a hc) CH)
    (tie : Closed (D3 3 𝒜) fun Fm _ => RealPlaceSecondLayerConditions Fm) :
    Closed (D3 3 𝒜) fun Fm CH => ∀ hc : D3 3 𝒜 Fm, Formalism.MainNotions.TuSize Fm → Formalism.MainNotions.DGamSize Fm → RemainingDivisionBounds Fm Cabs CH := by
  have hf := _root_.Formalism.L2.DIV.FunSharpTop.closed_funSharp_thr_alt 𝒜 sel selS selP selDH selC selB hRB hPA hDivG rRows
    Formalism.L2.DIV.SlopeMaxB.EbMu Formalism.MainNotions.DIV.HookProducts.Row4C.EcHH
  have hh : Closed (D3 3 𝒜) fun Fm CH => ∀ _ : D3 3 𝒜 Fm, Formalism.MainNotions.TuSize Fm → Formalism.MainNotions.DGamSize Fm →
      LocalQuadraticParts.ComplementTwoFamily Fm → DIVinN Fm → LocalQuadraticParts.FrameNumberBoundFamily Fm Fm.Csz CH :=
    (tie.and ((_root_.Formalism.L2.DIV.LinkGCl.closed_linkG_of_tuSize_dGamSize 𝒜 sel).and hf)).imp fun Fm CH _ h hc hTu hDG c2 hN => by
      obtain ⟨CF0, hL, he⟩ := h.2.2 hc hTu hDG
      have hE := Formalism.L2.DIV.LvlWire.lvlF_of_ties Fm h.1 hTu
      have hrk := Formalism.L2.DIV.LvlWire.muRank_of_lvl Fm (by norm_num : (0 : ℝ) < 3)
        (Formalism.L2.DIV.LvlWire.proviso_of_working_class Fm hc) hE hTu
      have lMu := Formalism.SlopeId.linkMu_of_full Fm hTu hDG (Formalism.L2.DIV.LvlWire.nuFullF_of_lvl Fm hE) hrk
      exact Formalism.L2.DIV.LvlWire.hh_of_lvl Fm CH Formalism.L2.DIV.SlopeMaxB.EbMu CF0 hL hE hTu hrk (h.2.1 hc hTu hDG) lMu c2
        (_root_.Formalism.L2.DIV.SlopeMaxB.eventually_muMax_le_pow_ebMu_mul_of_tuSize (sel Fm (d3_a hc)) hTu) (he hN)
  have br := _root_.Formalism.L2.DIV.RatFullFam.buRat_rrFull_closed_alt 𝒜 sel selS selP selDH selC selB hPA hDivG hDcPtG rRows
  exact (hh.and br).imp fun Fm _ _ h hc hT hD =>
    show RemainingDivisionBounds Fm Cabs _ from
      { hh := h.1 hc hT hD, bu := (h.2 hc hT hD).1, rr := (h.2 hc hT hD).2, la := Formalism.L2.DIV.Wire.la_of Fm }
end Formalism.L2.DIV.RestAll
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT Formalism.L2.Top3 Formalism.L2.Top4
theorem GlobalTheory.Top.link_brest_alt : ∀ (𝒜 : FamClass)
    (sel : _root_.Formalism.L2.TwistSelection 𝒜)
    (selS : _root_.Formalism.L2.Top4.SelectionSpectralCondition 𝒜 sel)
    (selP : _root_.Formalism.L2.Top4.BaseLevelTiedChoiceAlt 𝒜 sel)
    (selDH : _root_.Formalism.L2.Top3.SelectionDefiniteHeightCondition 𝒜 sel)
    (selC : _root_.Formalism.L2.Top4.ColumnChoiceCompatibleSelection 𝒜 sel selP)
    (selB : _root_.Formalism.L2.Top4.SelectionBundle 𝒜 sel selS selP selDH selC)
    (hRB : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      _root_.Formalism.IndefR.IndefiniteRealisationBoundedRows (selB Fm hc x hx h i))
    (hPA : _root_.Formalism.L2.Top4.AllRealisationsPrimitive sel (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB))
    (hDivG : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.DIV.DivRows3G (selP Fm hc x hx h i).1)
    (hDcPtG : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.DIV.DcPtG (selP Fm hc x hx h i).1)
    (rRows : Closed (D3 3 𝒜) fun Fm CH => ∀ hc : D3 3 𝒜 Fm, _root_.Formalism.L2.Top4.RowsAtSelAlt sel (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) (fun Fm hc x hx h i C CH => _root_.Formalism.L2.Top4Wire2.DefRowsFAlt (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) Fm hc x hx h i C CH) (_root_.Formalism.L2.Top4.SingleMapCondition selB)
        Fm (d3_a hc) CH)
    (tie : Closed (D3 3 𝒜) fun Fm _ => RealPlaceSecondLayerConditions Fm), Closed (D3 3 𝒜) fun Fm CH => ∀ hc : D3 3 𝒜 Fm, TuSize Fm → DGamSize Fm → RemainingDivisionBounds Fm 2 CH :=
  fun 𝒜 sel selS selP selDH selC selB hRB hPA hDivG hDcPtG rRows tie =>
    _root_.Formalism.L2.DIV.RestAll.bRest_all_alt 𝒜 2 sel selS selP selDH selC selB hRB hPA hDivG hDcPtG rRows tie
end
