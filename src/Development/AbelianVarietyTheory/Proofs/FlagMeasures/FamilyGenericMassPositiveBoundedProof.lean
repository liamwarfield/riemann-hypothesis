module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DifferentLocalIdentityFamiliesLemmaH
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MatchedFamilyMassLawBaseSituation
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericMassLeHeightPowMulGluedCount
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FormulaExplicitAtOfEta
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcAllC
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.RealBracketOfRowBlock
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowFormAllOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RhsWLimOfLeaves

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeanCountConstantEqUnscaledMainConstant
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaugeVolUD
namespace GlobalTheory.GaugeVolumeUD

theorem gaugeVolUD : PI.AprimeInfW.GaugeVolUD := fun k => Formalism.L2.SG.Pf.GV.gaugeVolU k

instance : Fact (PI.AprimeInfW.GaugeVolUD) := ⟨gaugeVolUD⟩

end GlobalTheory.GaugeVolumeUD
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeanCountConstantEqUnscaledMainConstant
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CountConst

def emptyPairs {D : D7} (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂ where
  P := Empty
  fst := Empty.elim
  snd := Empty.elim
  row := fun p => p.elim
  inj := fun p => p.elim
  gscal := fun _ => False


set_option maxHeartbeats 4000000 in
theorem countConst_eq_unscaledConst : PI.VolStabS.MassDataS.SWXS → ∀ (Cg cb Cw cT CT C0 C' Cl : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' → 2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k → (D.mem u).A.T ≡ (D.mem u').A.T [MOD (gS D) ^ 2] → ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ → ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf), 0 < Formalism.L2.SG.MassDataConc.ngFac D ∧ Formalism.L2.SG.Pf.Cnt.cExpl D (X.Fu u) (Y.what₂ u) * Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) (Y.what₂ u) * ∏' p, Formalism.L2.SG.DataInst.alpD u u' p = (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).AA * Formalism.L2.SG.MassDataConc.ngFac D := by
  intro hSW Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc hk hcong hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq
  obtain ⟨hMT, hI, hS, hMC, hLC, hLT, hdet⟩ := hT
  set Q0 := emptyPairs u u' (X.Fu u) (Y.what₂ u) with hQ0
  set vR0 : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℝ := fun _ => 0 with hvR0
  have hK2 := Formalism.L2.SG.Closed.level_subgroup_properties X
  have hV : 0 < X.volK2 := ENNReal.toReal_pos (ne_of_gt hK2.2.2.1) (ne_of_lt hK2.2.2.2)
  have hH : Formalism.L2.SG.TypedSets.HypX X hb (Y.FN u) (Y.FN u') u u' := ⟨hMT, hK2, Y.FN_fund u, Y.FN_fund u'⟩
  have hStd : Formalism.L2.SG.LocVol.StdHyp X.B.I.cm.sig X.B.I.J ψ :=
    ⟨MassDataVolumesW.stepCM X, MassDataVolumesW.stepHerm X, hI, hS⟩
  have hlat : ∃ L : Submodule (NumberField.RingOfIntegers X.B.I.E) (Fin X.B.I.n → X.B.I.E),
      Submodule.IsFullLattice X.B.I.E L ∧
      (L : Set (Fin X.B.I.n → X.B.I.E)) = (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :=
    ⟨X.B.I.L, ⟨{ toIsLattice := Submodule.IsLattice.of_fg X.B.I.E X.B.I.L_fg,
                     span_eq_top := X.B.I.L_span }, rfl⟩⟩
  have hdet' : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.gramE X.B.I.cm.sig X.B.I.J
      (Formalism.L2.SG.Sub.tupH (Formalism.L2.SG.TypedSets.frameOf X u'))).det ≠ 0 :=
    Formalism.L2.SG.Pf.Rescale.standard_gram_nondegenerate X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J _ _ _
      (fun x => star_star x) hStd.2.1 (Formalism.L2.SG.Pf.Rescale.frame_stdX X u')
  have hPC := Formalism.L2.SG.Pf.ProdConvCut2.prodConv_holds_gen X hb ψ hI hS hLC u u'
  have hL := Formalism.L2.SG.LocVol.locTieX_of X ψ u (hLC u) (Formalism.L2.SG.Pf.LocVolPrim.primX X u locFramePrim)
  have hL' := Formalism.L2.SG.LocVol.locTieX_of X ψ u' (hLC u') (Formalism.L2.SG.Pf.LocVolPrim.primX X u' locFramePrim)
  have hTF := Formalism.L2.SG.Pf.typFacts_holds X hb u u'
  have hQ := Formalism.L2.SG.Pf.MassDataPos.quotVolPosC_of X hb Y u u' X0 ψ (Y.tO u u') 0 0 1 vR0 Q0 Y.M Y.δ i0 i0' νq hK2 hV
  have hN := Formalism.L2.SG.Pf.NcAllC.ncTieC_of_closed X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') 0 0 1 vR0 Q0
    Y.M Y.δ i0 i0' νq Formalism.L2.SG.Closed.CovolRef_outright hSW hH hMC hStd hlat hdet' hdet hPC hL hL' hTF hQ le_rfl le_rfl
    one_pos hcong (Y.rowsOK u)
  have hρ := Formalism.L2.SG.MassDataConc.RhoTieC_closed X hb Y u u' X0 ψ 0 0 1 vR0 Q0 Y.M Y.δ i0 i0' νq
  have hal := Formalism.L2.SG.Pf.AlTie.locOf_al_eq X (Formalism.L2.SG.Pf.AlTie.etaTie_of X hLT) hk u u' ψ
  have hκ := Formalism.L2.SG.WConst.kapN_pos (D := D)
  have hng := Formalism.L2.SG.Pf.ngFac_pos D
  have hρp := Formalism.L2.SG.RhoPf.massRows_pos X Y u
  have hαp := Formalism.L2.SG.PoincareAmplitudeLowerBounds.tprod_alpD_pos D hk u u'
  refine ⟨hng, ?_⟩
  set B0 := Formalism.L2.SG.MassDataConc.bCF X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') 0 0 1 vR0 Q0 Y.M Y.δ i0 i0' νq
    with hB0
  have eU : kapU D = Formalism.L2.SG.MassDataConc.kapN D := if_pos hκ
  have eA : (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).AA = B0.AA / kapU D := by
    show B0.volB * (B0.Coo / kapU D) * (B0.MM / B0.volZZ) / B0.μK =
      B0.volB * B0.Coo * (B0.MM / B0.volZZ) / B0.μK / kapU D
    ring
  have en : B0.n0c = B0.AA / B0.ρ0 := rfl
  have eal : B0.al = ∏' q, Formalism.L2.SG.DataInst.alpD u u' q := hal
  have eρ : B0.ρ0 = Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) (Y.what₂ u) := hρ
  have key : Formalism.L2.SG.Pf.Cnt.cExpl D (X.Fu u) (Y.what₂ u) =
      B0.n0c * Formalism.L2.SG.MassDataConc.ngFac D / (B0.al * Formalism.L2.SG.MassDataConc.kapN D) := hN
  rw [key, en, eρ, eal, eA, eU]
  field_simp

end GlobalTheory.CountConst
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeanCountConstantEqUnscaledMainConstantStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.meanCountConstant_eq_unscaledMainConstant : PI.VolStabS.MassDataS.SWXS → ∀ (Cg cb Cw cT CT C0 C' Cl : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' → 2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k → (D.mem u).A.T ≡ (D.mem u').A.T [MOD (gS D) ^ 2] → ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ → ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf), 0 < Formalism.L2.SG.MassDataConc.ngFac D ∧ Formalism.L2.SG.Pf.Cnt.cExpl D (X.Fu u) (Y.what₂ u) * Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) (Y.what₂ u) * ∏' p, Formalism.L2.SG.DataInst.alpD u u' p = (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).AA * Formalism.L2.SG.MassDataConc.ngFac D := by
  first | exact @GlobalTheory.CountConst.countConst_eq_unscaledConst | exact GlobalTheory.CountConst.countConst_eq_unscaledConst | (intros; apply GlobalTheory.CountConst.countConst_eq_unscaledConst <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluedLatticeWeightedCountLeExplicit
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluedLatticeWeightedCountLeExplicit
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
open ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.GlueCount

def locSpOf {D : D7} (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ p, Agree δ M p) : Formalism.L2.SG.CntLocal.LocSp D M where
  V := Vp D
  H p := locHerm M p (hA p).2.2.1
  rank := finrank_Vp
  bc := baseChange₂ D
  bc_smul := baseChange_smul₂
  bc_span := span_baseChange_eq_top
  bc_form p x y := baseChangeAt_form M p (hA p).2.2.1 x y

theorem exists_unif_at {D : D7} (p : PlF D) : ∃ ϖ : 𝒪[(D.s.atP p).Fp], Irreducible ϖ := by
  haveI := (D.s.atP p).lf
  exact IsDiscreteValuationRing.exists_irreducible _

theorem exists_unifs (D : D7) : ∃ ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp], ∀ p, Irreducible (ϖ p) :=
  ⟨fun p => (exists_unif_at p).choose, fun p => (exists_unif_at p).choose_spec⟩

theorem one_mem_stabFix {D : D7} (U : Submodule D.host.E (VS D).V) (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ Formalism.L2.SG.Pf.Cnt.stabFix (VS D).hT U Λ := by
  refine ⟨(Formalism.L2.SG.Pf.Cnt.isomFix (VS D).hT U).one_mem, ?_⟩
  ext x
  simp [Formalism.HermitianLatticesTheory.gmap]

section Reps
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.Asm Formalism.L2.SG.CntLocal Module

theorem exists_glueReps (D : D7) (u u' : D.what₂.Word) (hT : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (gS D) ^ 2])
    (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (hR : IsRowReps D F0 what₂)
    (G' : LFlag (D.sp.Y 0) D.R.rS (Tn u')) (hz : G'.zt = G'.fl.z) (hP : Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') (ZhatL (lf D F0) G'))) :
    ∃ s, IsGlueReps (VS D).hT (UPair D F0 G') (MMof D F0 G') s := by
  haveI : Fact HermRepUnram := ⟨GlobalTheory.BinaryRep.represents_totallyPositive⟩
  obtain ⟨hLat, -⟩ := mmChar_of local_unimodular_holds D u u' hT F0 what₂ hR _ G' hz rfl hP
  by_cases hI : Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (MMof D F0 G')
  · obtain ⟨hK, hF, hN⟩ := field_dictionary_holds D
    obtain ⟨hC, hPD, hUr, hWr⟩ := perpendicular_definition_holds D u u' hT F0 what₂ hR _ G' hz rfl hP
    have hk : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
    have hcJ : ∀ 𝔭 : Ideal (𝓞 D.host.F), 𝔭.IsMaximal →
        cJ (VS D).hT (UPair D F0 G') (MMof D F0 G') 𝔭 < finrank D.host.E (orthK (VS D).hT (UPair D F0 G')) := by
      intro 𝔭 _
      have := cJ_le (VS D).hT (UPair D F0 G') (MMof D F0 G') 𝔭
      rw [hWr]
      omega
    have hne := glueExists_holds D.host.E D.host.F (VS D).V hK hF (VS D).hT (VS D).herm hN (UPair D F0 G') hC hPD
      ⟨(VS D).L0, (VS D).standardTuple_isLattice, (VS D).baseLattice_isUnimodular⟩ (MMof D F0 G') hLat hI hcJ
    have hMC : MassConst D.host.E D.host.F (finrank D.host.E (orthK (VS D).hT (UPair D F0 G')))
        (cMass D.host.E D.host.F (D.R.k - 1)) := by
      rw [hWr]
      exact (cMass_spec hK hF (D.R.k - 1) (by omega)).2
    obtain ⟨s, hs1, hs2, hs3, -⟩ := gluing_mass_holds D.host.E D.host.F (VS D).V hK hF (VS D).hT (VS D).herm hN
      (UPair D F0 G') hC hPD (MMof D F0 G') hLat hI hne _ hMC
    exact ⟨s, hs1, hs2, hs3⟩
  · exact ⟨∅, isGlueReps_empty (glueSet_eq_empty (U := UPair D F0 G') hI)⟩

end Reps

theorem glueSum_le : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.L2.SG.Pf.LocCP.LocTied D → 2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k → (D.mem u).A.T ≡ (D.mem u').A.T [MOD (gS D) ^ 2] → ∀ G' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E), G'.zt = G'.fl.z → TotPos (Gval (lf D (X.Fu u)) G') → ∃ s : Finset (LV D), Glue (lf D (X.Fu u)) G' s ∧ (s.Nonempty → (∃ Λ, IsRowLat D (X.Fu u) Λ ∧ G' ∈ Formalism.L2.SG.CntLocal.EZ ((Tu D u' : ℕ) : D.host.E) (X.Fu u) Λ (ZhatL (lf D (X.Fu u)) G')) ∧ glueSum (lf D (X.Fu u)) G' s ≤ 2 * (Formalism.L2.SG.Pf.Cnt.cExpl D (X.Fu u) (Y.what₂ u) * Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) (Y.what₂ u) * ∏' p, Formalism.L2.SG.DataInst.alpD u u' p) * Formalism.L2.SG.CntLocal.sqrtAbsNormOfScaledGram ((Tu D u : ℕ) : D.host.E) ((Tu D u' : ℕ) : D.host.E) (ZhatL (lf D (X.Fu u)) G') ^ (D.R.k - 1)) := by
  intro D X Y u u' hTied hk hT G' hz hTP
  haveI : Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram := ⟨GlobalTheory.BinaryRep.represents_totallyPositive⟩
  have hR : IsRowReps D (X.Fu u) (Y.what₂ u) := Y.rowsOK u
  have hP : Formalism.MainNotions.S.LocalSplitGroups.TotPos (Formalism.L2.SG.CntLocal.GZ (Formalism.L2.SG.CntLocal.Tn u) (Formalism.L2.SG.CntLocal.Tn u')
      (ZhatL (lf D (X.Fu u)) G')) := hTP
  obtain ⟨s, hs⟩ := exists_glueReps D u u' hT (X.Fu u) (Y.what₂ u) hR G' hz hP
  obtain ⟨-, hchar⟩ := Formalism.L2.SG.Pf.Cnt.mmChar_of Formalism.L2.SG.Pf.Cnt.local_unimodular_holds D u u' hT (X.Fu u) (Y.what₂ u) hR _ G'
    hz rfl hP
  have e4 := Formalism.L2.SG.Pf.Cnt.lattice_groupoid_holds D u u' hT (X.Fu u) (Y.what₂ u) hR _ G' hz rfl hP s hs
  refine ⟨s, hs, fun hne => ?_⟩
  obtain ⟨Λ, hΛ⟩ := hne
  refine ⟨⟨Λ, (hchar Λ).2 (hs.1 Λ hΛ)⟩, ?_⟩
  have hsum : glueSum (lf D (X.Fu u)) G' s = Formalism.L2.SG.CntLocal.nu (Formalism.L2.SG.CntLocal.Tn u') (X.Fu u) (Y.what₂ u)
      (ZhatL (lf D (X.Fu u)) G') * Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) (Y.what₂ u) := by
    exact e4.symm
  have hpos : 0 < glueSum (lf D (X.Fu u)) G' s := by
    unfold glueSum
    refine Finset.sum_pos (fun Λ' hΛ' => ?_) ⟨Λ, hΛ⟩
    haveI : Finite (Formalism.L2.SG.Pf.Cnt.stabFix (VS D).hT (Formalism.L2.SG.Pf.Cnt.UPair D (X.Fu u) G') Λ') :=
      (hs.2.2 Λ' hΛ').to_subtype
    haveI : Nonempty (Formalism.L2.SG.Pf.Cnt.stabFix (VS D).hT (Formalism.L2.SG.Pf.Cnt.UPair D (X.Fu u) G') Λ') :=
      ⟨⟨1, one_mem_stabFix _ _⟩⟩
    exact inv_pos.2 (Nat.cast_pos.2 Nat.card_pos)
  have hnu : Formalism.L2.SG.CntLocal.nu (Formalism.L2.SG.CntLocal.Tn u') (X.Fu u) (Y.what₂ u) (ZhatL (lf D (X.Fu u)) G') ≠ 0 := by
    intro h0
    rw [hsum, h0, zero_mul] at hpos
    exact lt_irrefl _ hpos
  have hrow : ∃ Λ₁ ∈ Y.what₂ u,
      (Formalism.L2.SG.CntLocal.EZ (Formalism.L2.SG.CntLocal.Tn u') (X.Fu u) Λ₁ (ZhatL (lf D (X.Fu u)) G')).Nonempty := by
    by_contra hno
    push_neg at hno
    apply hnu
    unfold Formalism.L2.SG.CntLocal.nu
    rw [Finset.sum_eq_zero (fun Λ₁ h1 => by simp [Formalism.L2.SG.CntLocal.cntE, hno Λ₁ h1]), zero_div]
  obtain ⟨ϖ, hϖ⟩ := exists_unifs D
  have hfe := Formalism.L2.SG.Pf.formulaExplicitAt_of_eta D Formalism.L2.SG.Pf.Cnt.DualityBasisChange.frameBasisL_holds
    (fun p => Formalism.L2.SG.Pf.AlTieLG.etaLoc_of_tied hTied p) Y.δ Y.M Y.agree (locSpOf Y.δ Y.M Y.agree) u u' hT
    (X.Fu u) (Y.what₂ u) hR ϖ hϖ _ hP
  obtain ⟨-, hbdd, -, hαpos, hDI⟩ := Formalism.L2.SG.Pf.Cnt.densInputT_holds D hTied hk Y.δ Y.M Y.agree
    (locSpOf Y.δ Y.M Y.agree) u u' hT (X.Fu u) (Y.what₂ u) hR ϖ hϖ
  obtain ⟨hk2, P, q, l, hl, hS, hx⟩ := hDI
  have hsd := (Formalism.FourierDecayAlt.Final.tc_densChain Formalism.FourierDecayAlt.Final.tc_densSum Formalism.FourierDecayAlt.Final.tc_densLeTwo
    Formalism.FourierDecayAlt.Final.tc_densSize P q l _ _ _ _ hk2 hl hS hx).2
  have hdle : ∏' p, Formalism.L2.SG.CntLocal.densP (locSpOf Y.δ Y.M Y.agree) Y.δ ϖ (Formalism.L2.SG.CntLocal.Tn u)
      (Formalism.L2.SG.CntLocal.Tn u') (ZhatL (lf D (X.Fu u)) G') p ≤ 2 * ∏' p, Formalism.L2.SG.DataInst.alpD u u' p :=
    (le_csSup hbdd ⟨_, hrow, rfl⟩).trans ((div_le_iff₀ hαpos).1 hsd)
  obtain ⟨Λ₁, hΛ₁, -⟩ := hrow
  have hc : 0 < Formalism.L2.SG.Pf.Cnt.cExpl D (X.Fu u) (Y.what₂ u) :=
    Formalism.L2.SG.Pf.Cnt.cExpl_pos' D u (X.Fu u) (Y.what₂ u) hR ⟨Λ₁, hΛ₁⟩
  have hm : 0 ≤ Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) (Y.what₂ u) :=
    Finset.sum_nonneg (fun _ _ => by unfold Formalism.MainNotions.S.wRow; positivity)
  have hN : 0 ≤ Formalism.L2.SG.CntLocal.sqrtAbsNormOfScaledGram ((Tu D u : ℕ) : D.host.E) ((Tu D u' : ℕ) : D.host.E)
      (ZhatL (lf D (X.Fu u)) G') := Real.sqrt_nonneg _
  have hfe' : Formalism.L2.SG.CntLocal.nu (Formalism.L2.SG.CntLocal.Tn u') (X.Fu u) (Y.what₂ u) (ZhatL (lf D (X.Fu u)) G') =
      Formalism.L2.SG.Pf.Cnt.cExpl D (X.Fu u) (Y.what₂ u) * Formalism.L2.SG.CntLocal.sqrtAbsNormOfScaledGram ((Tu D u : ℕ) : D.host.E)
        ((Tu D u' : ℕ) : D.host.E) (ZhatL (lf D (X.Fu u)) G') ^ (D.R.k - 1) *
      ∏' p, Formalism.L2.SG.CntLocal.densP (locSpOf Y.δ Y.M Y.agree) Y.δ ϖ (Formalism.L2.SG.CntLocal.Tn u)
        (Formalism.L2.SG.CntLocal.Tn u') (ZhatL (lf D (X.Fu u)) G') p := hfe
  rw [hsum, hfe']
  calc _ = (Formalism.L2.SG.Pf.Cnt.cExpl D (X.Fu u) (Y.what₂ u) * Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) (Y.what₂ u) *
        Formalism.L2.SG.CntLocal.sqrtAbsNormOfScaledGram ((Tu D u : ℕ) : D.host.E) ((Tu D u' : ℕ) : D.host.E)
          (ZhatL (lf D (X.Fu u)) G') ^ (D.R.k - 1)) *
        ∏' p, Formalism.L2.SG.CntLocal.densP (locSpOf Y.δ Y.M Y.agree) Y.δ ϖ (Formalism.L2.SG.CntLocal.Tn u)
          (Formalism.L2.SG.CntLocal.Tn u') (ZhatL (lf D (X.Fu u)) G') p := by ring
    _ ≤ (Formalism.L2.SG.Pf.Cnt.cExpl D (X.Fu u) (Y.what₂ u) * Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) (Y.what₂ u) *
        Formalism.L2.SG.CntLocal.sqrtAbsNormOfScaledGram ((Tu D u : ℕ) : D.host.E) ((Tu D u' : ℕ) : D.host.E)
          (ZhatL (lf D (X.Fu u)) G') ^ (D.R.k - 1)) * (2 * ∏' p, Formalism.L2.SG.DataInst.alpD u u' p) :=
      mul_le_mul_of_nonneg_left hdle (by positivity)
    _ = _ := by ring

end GlobalTheory.GlueCount
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluedLatticeWeightedCountLeExplicitStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gluedLattice_weightedCount_le_explicit : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.L2.SG.Pf.LocCP.LocTied D → 2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k → (D.mem u).A.T ≡ (D.mem u').A.T [MOD (gS D) ^ 2] → ∀ G' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E), G'.zt = G'.fl.z → TotPos (Gval (lf D (X.Fu u)) G') → ∃ s : Finset (LV D), Glue (lf D (X.Fu u)) G' s ∧ (s.Nonempty → (∃ Λ, IsRowLat D (X.Fu u) Λ ∧ G' ∈ Formalism.L2.SG.CntLocal.EZ ((Tu D u' : ℕ) : D.host.E) (X.Fu u) Λ (ZhatL (lf D (X.Fu u)) G')) ∧ glueSum (lf D (X.Fu u)) G' s ≤ 2 * (Formalism.L2.SG.Pf.Cnt.cExpl D (X.Fu u) (Y.what₂ u) * Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) (Y.what₂ u) * ∏' p, Formalism.L2.SG.DataInst.alpD u u' p) * Formalism.L2.SG.CntLocal.sqrtAbsNormOfScaledGram ((Tu D u : ℕ) : D.host.E) ((Tu D u' : ℕ) : D.host.E) (ZhatL (lf D (X.Fu u)) G') ^ (D.R.k - 1)) := by
  first | exact @GlobalTheory.GlueCount.glueSum_le | exact GlobalTheory.GlueCount.glueSum_le | (intros; apply GlobalTheory.GlueCount.glueSum_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormsInvariantsGenericRationalFramePair
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormsInvariantsGenericRationalFramePair
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GenMass.Norms

theorem sqrt_norm_eq (D : D7) (x : D.host.E) :
    Real.sqrt |((Algebra.norm ℚ x : ℚ) : ℝ)| = ∏ w : InfinitePlace D.host.E, w x := by
  have := Formalism.MainNotions.InterlacingSignCuts.host_totallyComplex D
  have h1 := InfinitePlace.prod_eq_abs_norm x
  have h2 : ∏ w : InfinitePlace D.host.E, w x ^ w.mult = (∏ w : InfinitePlace D.host.E, w x) ^ 2 := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun w _ => by rw [(IsTotallyComplex.isComplex w).mult_eq_two]
  rw [← Rat.cast_abs, ← h1, h2]
  exact Real.sqrt_sq (Finset.prod_nonneg fun w _ => w.1.nonneg _)

theorem prod_natPow (D : D7) (g m : ℕ) :
    ∏ w : InfinitePlace D.host.E, w ((g : D.host.E) ^ m) = ((g : ℝ) ^ m) ^ D.R.f := by
  rw [← Formalism.MainNotions.LatticeGluingRadicals.d_card D, ← Finset.card_univ, ← Finset.prod_const]
  exact Finset.prod_congr rfl fun w _ => by rw [map_pow, InfinitePlace.map_natCast]

theorem localInvariantNorm_eq_prod_infinitePlaces_div (D : D7) (T T' : D.host.E) (Z : Formalism.L2.SG.CntLocal.MatZ D) :
    Formalism.L2.SG.CntLocal.sqrtAbsNormOfScaledGram T T' Z =
      (∏ w : InfinitePlace D.host.E, w (Formalism.L2.SG.CntLocal.GZ T T' Z)) / (((gS D : ℕ) : ℝ) ^ D.R.m) ^ D.R.f := by
  unfold Formalism.L2.SG.CntLocal.sqrtAbsNormOfScaledGram
  rw [sqrt_norm_eq, ← prod_natPow, ← Finset.prod_div_distrib]
  exact Finset.prod_congr rfl fun w _ => by rw [map_div₀]

theorem rd_pow_f (D : D7) : D.host.rdE ^ D.R.f = |(NumberField.discr D.host.F : ℝ)| := by
  have h := Formalism.MainNotions.BridgeLemma.szf_rd_pow D
  rw [Formalism.L2.SG.NGCut.LeadingMinorIntegrality.discr_sq] at h
  have hrd := Formalism.L2.SG.NGCut.LeadingMinorIntegrality.rd_pos (D := D)
  refine (pow_left_inj₀ (by positivity) (abs_nonneg _) two_ne_zero).1 ?_
  rw [h]; push_cast; rw [abs_pow]

theorem one_le_tprod_real {ι : Type} (a : ι → ℝ) (ha : ∀ i, 1 ≤ a i) : 1 ≤ ∏' i, a i := by
  by_cases h : Multipliable a
  · refine ge_of_tendsto' h.hasProd fun s => ?_
    exact Finset.one_le_prod₀ (fun i _ => ha i)
  · rw [tprod_eq_one_of_not_multipliable h]

theorem one_le_nM {K V : Type} [Field K] [NumberField K] [StarRing K] (F : Type) [Field F] [NumberField F]
    [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (M : Submodule (𝓞 K) V) :
    1 ≤ Formalism.L2.SG.Pf.Cnt.nM F h U M := by
  unfold Formalism.L2.SG.Pf.Cnt.nM
  refine one_le_tprod_real _ fun p => one_le_pow₀ ?_
  have h0 : p.1 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField p.2 (RingOfIntegers.not_isField F)
  have h1 : Ideal.absNorm p.1 ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  exact_mod_cast Nat.one_le_iff_ne_zero.2 h1

theorem m_eq (D : D7) : D.R.m = 2 * D.R.rS + 2 := by
  obtain ⟨t, ht⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  unfold Ranks.rS
  omega

theorem norms_generic : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), (D.mem u).A.T ≡ (D.mem u').A.T [MOD (gS D) ^ 2] → ∀ (G' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (Λ : LV D) (w : Point D.host.E (D.R.rS + 1)), G'.zt = G'.fl.z → TotPos (Gval (lf D (X.Fu u)) G') → IsRowLat D (X.Fu u) Λ → G' ∈ Formalism.L2.SG.CntLocal.EZ ((Tu D u' : ℕ) : D.host.E) (X.Fu u) Λ (ZhatL (lf D (X.Fu u)) G') → IsInCell (ZhatOM (ZhatL (lf D (X.Fu u)) G')) w → (∀ a, 1 ≤ ∏ v : InfinitePlace D.host.E, (D.host.rdE ^ (2 * (endIdx (toPts w) a * (2 * D.R.rS + 1 - endIdx (toPts w) a))))⁻¹ * v (endMin (toPts w) a) ^ 2) ∧ ((gS D : ℝ)) ^ ((2 * D.R.rS + 2) * Fintype.card (InfinitePlace D.host.E)) ≤ NGPt D.host.rdE (Tu D u * Tu D u') (toPts w) ∧ Formalism.L2.SG.CntLocal.sqrtAbsNormOfScaledGram ((Tu D u : ℕ) : D.host.E) ((Tu D u' : ℕ) : D.host.E) (ZhatL (lf D (X.Fu u)) G') ^ (D.R.k - 1) * Formalism.L2.SG.MassDataConc.ngFac D = PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * NGPt D.host.rdE (Tu D u * Tu D u') (toPts w) ^ (D.R.k - 1) := by
  intro D X Y u u' hT G' Λ w hzt hP hrow hE hcell
  have hun := hrow.2.1.2.1
  have hz := hrow.2.1.2.2.1.1
  have hX := hrow.2.2
  have hz' : G'.fl.z ∈ Λ := hE.1.1.1
  have hX' := hE.2.2.2.1.2
  have hF : ∀ b, frame (lf D (X.Fu u)) b ∈ Λ := PtPf.frame_mem _ hz hX
  have hF' : ∀ b, frame G' b ∈ Λ := PtPf.frame_mem _ hz' hX'
  have hrd := Formalism.L2.SG.NGCut.LeadingMinorIntegrality.rd_pos (D := D)
  have hg : (0 : ℝ) < (gS D : ℕ) := by exact_mod_cast Formalism.MainNotions.LatticeGluingRadicals.z_gS_pos D
  have hGeq := LeadingMinorIntegrality.gpt_eq (T := Tu D u) (T' := Tu D u') (lf D (X.Fu u)) G' _ hcell
  set P : ℝ := ∏ v : InfinitePlace D.host.E, v (Gval (lf D (X.Fu u)) G') with hPdef
  have hNG : NGPt D.host.rdE (Tu D u * Tu D u') (toPts w) =
      ((D.host.rdE ^ D.R.f) ^ (2 * D.R.rS * (D.R.rS + 1)))⁻¹ * P := by
    unfold NGPt
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Formalism.MainNotions.LatticeGluingRadicals.d_card D, hGeq, inv_pow,
      ← pow_mul, ← pow_mul, mul_comm D.R.f]
    rfl
  have hN0 : Formalism.L2.SG.CntLocal.sqrtAbsNormOfScaledGram ((Tu D u : ℕ) : D.host.E) ((Tu D u' : ℕ) : D.host.E)
      (ZhatL (lf D (X.Fu u)) G') = P / (((gS D : ℕ) : ℝ) ^ D.R.m) ^ D.R.f := localInvariantNorm_eq_prod_infinitePlaces_div D _ _ _
  refine ⟨fun a => ?_, ?_, ?_⟩
  · have hj : endIdx (toPts w) a ≤ D.R.rS + 1 := (toPts w).1.sizeUpTo_le _
    obtain ⟨o, ho, e⟩ := LeadingMinorIntegrality.lead_mem hun (lf D (X.Fu u)) G' hz hX hz' hX' _ hj
    rw [← LeadingMinorIntegrality.lead_cell _ _ hcell, ← LeadingMinorIntegrality.endMin_eq] at e
    have hE5 := PtPf.blockEndMinors_of_cell _ (PtPf.zhatOM_isIntegral _ _ hun hF hF') _ hcell
    have h0 : endMin (toPts w) a ≠ 0 := (hE5 a).2
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Formalism.MainNotions.LatticeGluingRadicals.d_card D]
    have hsq := LeadingMinorIntegrality.prod_sq_ge _ o ho (by rw [e]; exact h0)
    rw [e] at hsq
    rw [inv_pow, ← div_eq_inv_mul, one_le_div (by positivity), ← pow_mul, mul_comm _ D.R.f, pow_mul]
    exact hsq
  · have hI := Formalism.L2.SG.Pf.Cnt.mmInt_of_EZ hT (Y.rowsOK u) hzt rfl hP hrow hE
    have hn := PI.UnitaryGroupMassFormula.CntFormula.R6.norm_mass_of_jordan D u u' hT (X.Fu u) (Y.what₂ u) (Y.rowsOK u) _ G' hzt rfl hP hI
    have h1 := one_le_nM D.host.F (VS D).hT (Formalism.L2.SG.Pf.Cnt.UPair D (X.Fu u) G')
      (Formalism.L2.SG.Pf.Cnt.MMof D (X.Fu u) G')
    replace h1 := h1.trans_eq hn
    rw [zpow_neg, zpow_natCast, ← rd_pow_f] at h1
    replace h1 : 1 ≤ ((D.host.rdE ^ D.R.f) ^ (2 * D.R.rS * (D.R.rS + 1)))⁻¹ *
        (P / (((gS D : ℕ) : ℝ) ^ D.R.m) ^ D.R.f) := hN0 ▸ h1
    rw [← mul_div_assoc, one_le_div (by positivity)] at h1
    rw [hNG, Formalism.MainNotions.LatticeGluingRadicals.d_card D, ← m_eq, pow_mul]
    exact h1
  · have hv : 2 * D.host.v = D.host.rdE := by unfold Host.v; ring
    rw [hN0, hNG, hv]
    unfold Formalism.L2.SG.MassDataConc.ngFac PN.abelian₂
    rw [sqrt_norm_eq, prod_natPow, ← mul_pow, div_mul_cancel₀ _ (by positivity)]
    have e : D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1) * (D.R.k - 1) * D.R.f) =
        ((D.host.rdE ^ D.R.f) ^ (2 * D.R.rS * (D.R.rS + 1))) ^ (D.R.k - 1) := by
      rw [← pow_mul, ← pow_mul]; congr 1; ring
    rw [e, ← mul_pow, mul_inv_cancel_left₀ (by positivity)]

end GlobalTheory.GenMass.Norms
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormsInvariantsGenericRationalFramePairStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norms_invariants_generic_rational_framePair : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), (D.mem u).A.T ≡ (D.mem u').A.T [MOD (gS D) ^ 2] → ∀ (G' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (Λ : LV D) (w : Point D.host.E (D.R.rS + 1)), G'.zt = G'.fl.z → TotPos (Gval (lf D (X.Fu u)) G') → IsRowLat D (X.Fu u) Λ → G' ∈ Formalism.L2.SG.CntLocal.EZ ((Tu D u' : ℕ) : D.host.E) (X.Fu u) Λ (ZhatL (lf D (X.Fu u)) G') → IsInCell (ZhatOM (ZhatL (lf D (X.Fu u)) G')) w → (∀ a, 1 ≤ ∏ v : InfinitePlace D.host.E, (D.host.rdE ^ (2 * (endIdx (toPts w) a * (2 * D.R.rS + 1 - endIdx (toPts w) a))))⁻¹ * v (endMin (toPts w) a) ^ 2) ∧ ((gS D : ℝ)) ^ ((2 * D.R.rS + 2) * Fintype.card (InfinitePlace D.host.E)) ≤ NGPt D.host.rdE (Tu D u * Tu D u') (toPts w) ∧ Formalism.L2.SG.CntLocal.sqrtAbsNormOfScaledGram ((Tu D u : ℕ) : D.host.E) ((Tu D u' : ℕ) : D.host.E) (ZhatL (lf D (X.Fu u)) G') ^ (D.R.k - 1) * Formalism.L2.SG.MassDataConc.ngFac D = PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * NGPt D.host.rdE (Tu D u * Tu D u') (toPts w) ^ (D.R.k - 1) := by
  first | exact @GlobalTheory.GenMass.Norms.norms_generic | exact GlobalTheory.GenMass.Norms.norms_generic | (intros; apply GlobalTheory.GenMass.Norms.norms_generic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagNormsCongrModLevelSq
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagNormsCongrModLevelSq
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt Formalism.L2.SG.NGData Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormCong

private theorem prime_dvd_int_of_cast_eq_mul {O : Type} [CommRing O] [IsDomain O] {ℓ : ℕ} (hℓ : ℓ.Prime) {q : O}
    (hq : Irreducible q) (hqℓ : q = (ℓ : O)) {m : ℤ} {c : O} (h : (m : O) = q * c) : (ℓ : ℤ) ∣ m := by
  by_contra hnd
  obtain ⟨a, b, hab⟩ := (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hℓ)).2 hnd
  apply hq.not_isUnit
  have h1 : ((a * ℓ + b * m : ℤ) : O) = 1 := by rw [hab]; simp
  push_cast at h1
  rw [h, ← hqℓ] at h1
  exact isUnit_iff_exists_inv.2 ⟨a + b * c, by linear_combination h1⟩

theorem int_sq_dvd_of_eq {O : Type} [CommRing O] [IsDomain O] {ℓ : ℕ} (hℓ : ℓ.Prime) {q : O} (hq : Irreducible q)
    (hqℓ : q = (ℓ : O)) {n : ℤ} {c : O} (h : (n : O) = q ^ 2 * c) : (ℓ : ℤ) ^ 2 ∣ n := by
  obtain ⟨m, rfl⟩ := prime_dvd_int_of_cast_eq_mul hℓ hq hqℓ (c := q * c) (by rw [h]; ring)
  push_cast at h
  rw [← hqℓ] at h
  have h2 : ((m : ℤ) : O) = q * c := by
    apply mul_left_cancel₀ hq.ne_zero
    rw [h]; ring
  obtain ⟨k, rfl⟩ := prime_dvd_int_of_cast_eq_mul hℓ hq hqℓ h2
  exact ⟨k, by ring⟩

theorem exists_place_resChar (K : Type) [Field K] [NumberField K] {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ∃ p : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Formalism.MainNotions.S.Loc.resChar p = ℓ := by
  haveI hmax : (Ideal.span {(ℓ : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hℓ).irreducible
  have hker : RingHom.ker (algebraMap ℤ (𝓞 K)) ≤ Ideal.span {(ℓ : ℤ)} := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (algebraMap ℤ (𝓞 K)).injective_int]
    exact bot_le
  obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 K) _ hker
  have hmem : ((ℓ : ℤ) : 𝓞 K) ∈ Q := by
    have h1 : (ℓ : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 K)) := by
      change (ℓ : ℤ) ∈ Ideal.under ℤ Q
      rw [hQc]
      exact Ideal.mem_span_singleton_self _
    simpa using h1
  have hne : Q ≠ ⊥ := by
    rintro rfl
    have h0 : ((ℓ : ℕ) : 𝓞 K) = 0 := by simpa using hmem
    exact hℓ.ne_zero (Nat.cast_eq_zero.mp h0)
  refine ⟨⟨Q, hQ.isPrime, hne⟩, ?_⟩
  haveI := hQ
  show ringChar (𝓞 K ⧸ Q) = ℓ
  have hz : ((ℓ : ℕ) : 𝓞 K ⧸ Q) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk Q), Ideal.Quotient.eq_zero_iff_mem]
    simpa using hmem
  rcases (Nat.dvd_prime hℓ).1 ((ringChar.spec _ ℓ).1 hz) with h1 | h1
  · exact absurd h1 CharP.ringChar_ne_one
  · exact h1

theorem sq_dvd_at (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (Tn T'n : ℕ)
    (F : LFlag (D.sp.Y 0) D.R.rS (Tn : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (T'n : D.host.E))
    (hB : Based Z FP Tn T'n F F') (hN : ∀ p, (FP p).NormsOK) (i : Fin 2) :
    ((D.host.g i : ℕ) : ℤ) ^ 2 ∣ (Tn : ℤ) - T'n := by
  obtain ⟨p, hp⟩ := exists_place_resChar D.host.F (D.host.g_prime i)
  have hsome : ((D.s.atP p).split).isSome := by
    rw [D.s_split p, hp]
    fin_cases i <;> simp
  obtain ⟨sg, hsg⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨-, -, -, -, -, hm⟩ := Z.agree p
  rcases hg : (Z.M p).split with _ | g
  · rw [hg, hsg] at hm
    exact (hm : False).elim
  rw [hg, hsg] at hm
  obtain ⟨-, hq⟩ := hm
  obtain ⟨-, -, -, -, hG⟩ := hN p
  obtain ⟨-, c, hc⟩ := hG g hg
  obtain ⟨-, -, hA, hB'⟩ := hB p
  refine int_sq_dvd_of_eq (D.host.g_prime i) g.q_irr ?_ (c := c) ?_
  · apply Subtype.ext
    rw [hq, sg.q_eq, hp]
    simp
  · apply Subtype.ext
    push_cast
    rw [← hA, ← hB']
    exact hc

end GlobalTheory.NormCong

open GlobalTheory.NormCong in
theorem GlobalTheory.NormCong.norms_congr : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (u u' : D.what₂.Word) (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).NormsOK) → (D.mem u).A.T ≡ (D.mem u').A.T [MOD (gS D) ^ 2] := by
  intro D Z FP u u' F F' hB hN
  have h0 := sq_dvd_at D Z FP (Tu D u) (Tu D u') F F' hB hN 0
  have h1 := sq_dvd_at D Z FP (Tu D u) (Tu D u') F F' hB hN 1
  have hcop : IsCoprime (((D.host.g 0 : ℕ) : ℤ) ^ 2) (((D.host.g 1 : ℕ) : ℤ) ^ 2) := by
    apply IsCoprime.pow
    exact Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)
  have h := dvd_sub_comm.1 (hcop.mul_dvd h0 h1)
  rw [Nat.modEq_iff_dvd, show gS D = D.host.g 0 * D.host.g 1 from rfl]
  push_cast
  rw [mul_pow]
  exact h
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagNormsCongrModLevelSqStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt Formalism.L2.SG.NGData Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagNorms_congr_mod_level_sq : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (u u' : D.what₂.Word) (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).NormsOK) → (D.mem u).A.T ≡ (D.mem u').A.T [MOD (gS D) ^ 2] := by
  first | exact @GlobalTheory.NormCong.norms_congr | exact GlobalTheory.NormCong.norms_congr | (intros; apply GlobalTheory.NormCong.norms_congr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramInvariantPowLeHaarWeight
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramInvariantPowLeHaarWeight
open NumberField Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Finset

namespace GlobalTheory.HaarWeight

theorem filter_lt_succ {p n : ℕ} (h : n < p) :
    (univ.filter fun b : Fin p => b.1 < n + 1) = insert ⟨n, h⟩ (univ.filter fun b : Fin p => b.1 < n) := by
  ext b
  simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
  omega

theorem filter_le_eq {p : ℕ} (a : Fin p) :
    (univ.filter fun b : Fin p => b ≤ a) = univ.filter fun b : Fin p => b.1 < a.1 + 1 := by
  ext b
  simp only [mem_filter, mem_univ, true_and, Fin.le_def]
  omega

private theorem one_le_partial_lemma (T : ℕ → ℝ) (m : ℕ → ℕ) (M p : ℕ) (hT : ∀ a, 0 ≤ T a)
    (hN : ∀ a < p, 1 ≤ ∏ b ∈ range (a + 1), T b) (hm : ∀ a, m a ≤ M) :
    ∀ k ≤ p, ∀ j ≤ M, (∏ b ∈ range k, T b) ^ j ≤
      (∏ a ∈ range k, ∏ b ∈ range (a + 1), T b) ^ M * ∏ a ∈ range k, T a ^ m a := by
  intro k
  induction k with
  | zero => intro _ j _; simp
  | succ k ih =>
    intro hk j hj
    have hP1 : 1 ≤ ∏ b ∈ range (k + 1), T b := hN k (by omega)
    have hQ := ih (by omega) (m k) (hm k)
    have hnn : 0 ≤ (∏ b ∈ range (k + 1), T b) ^ M * T k ^ m k :=
      mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg (hT k) _)
    calc (∏ b ∈ range (k + 1), T b) ^ j ≤ (∏ b ∈ range (k + 1), T b) ^ (m k + M) :=
          pow_le_pow_right₀ hP1 (by have := hm k; omega)
      _ = (∏ b ∈ range k, T b) ^ m k * ((∏ b ∈ range (k + 1), T b) ^ M * T k ^ m k) := by
          rw [pow_add, Finset.prod_range_succ]; ring
      _ ≤ ((∏ a ∈ range k, ∏ b ∈ range (a + 1), T b) ^ M * ∏ a ∈ range k, T a ^ m a) *
            ((∏ b ∈ range (k + 1), T b) ^ M * T k ^ m k) := mul_le_mul_of_nonneg_right hQ hnn
      _ = (∏ a ∈ range (k + 1), ∏ b ∈ range (a + 1), T b) ^ M * ∏ a ∈ range (k + 1), T a ^ m a := by
          rw [Finset.prod_range_succ (fun a => ∏ b ∈ range (a + 1), T b),
            Finset.prod_range_succ (fun a => T a ^ m a)]
          ring

theorem one_le_partial {p : ℕ} (T : Fin p → ℝ) (m : Fin p → ℕ) (M : ℕ)
    (hN : ∀ a : Fin p, 1 ≤ ∏ b ∈ univ.filter (fun b : Fin p => b ≤ a), T b) (hT : ∀ a, 0 ≤ T a)
    (hm : ∀ a, m a ≤ M) :
    1 ≤ (∏ a : Fin p, ∏ b ∈ univ.filter (fun b : Fin p => b ≤ a), T b) ^ M * ∏ a, T a ^ m a := by
  classical
  let T' : ℕ → ℝ := fun b => if h : b < p then T ⟨b, h⟩ else 1
  let m' : ℕ → ℕ := fun b => if h : b < p then m ⟨b, h⟩ else 0
  have hT' : ∀ b, 0 ≤ T' b := by
    intro b
    simp only [T']
    split_ifs
    · exact hT _
    · norm_num
  have hm' : ∀ b, m' b ≤ M := by
    intro b
    simp only [m']
    split_ifs
    · exact hm _
    · exact Nat.zero_le _
  have hTT : ∀ b : Fin p, T b = T' b := fun b => by simp [T', b.2]
  have hmm : ∀ b : Fin p, m b = m' b := fun b => by simp [m', b.2]
  have hpre : ∀ a : Fin p, ∏ b ∈ univ.filter (fun b : Fin p => b ≤ a), T b =
      ∏ b ∈ range (a.1 + 1), T' b := by
    intro a
    have ha := a.2
    rw [filter_le_eq, Finset.prod_filter]
    simp_rw [hTT]
    rw [Fin.prod_univ_eq_prod_range (fun i => if i < a.1 + 1 then T' i else 1) p, ← Finset.prod_filter]
    congr 1
    ext i
    simp only [mem_filter, mem_range]
    omega
  have hN' : ∀ a < p, 1 ≤ ∏ b ∈ range (a + 1), T' b := fun a ha => (hpre ⟨a, ha⟩) ▸ hN ⟨a, ha⟩
  have key := one_le_partial_lemma T' m' M p hT' hN' hm' p le_rfl 0 (Nat.zero_le _)
  rw [pow_zero] at key
  have e1 : (∏ a : Fin p, ∏ b ∈ univ.filter (fun b : Fin p => b ≤ a), T b) =
      ∏ a ∈ range p, ∏ b ∈ range (a + 1), T' b := by
    rw [← Fin.prod_univ_eq_prod_range (fun i => ∏ b ∈ range (i + 1), T' b) p]
    exact Finset.prod_congr rfl fun a _ => hpre a
  have e2 : (∏ a : Fin p, T a ^ m a) = ∏ a ∈ range p, T' a ^ m' a := by
    rw [← Fin.prod_univ_eq_prod_range (fun i => T' i ^ m' i) p]
    exact Finset.prod_congr rfl fun a _ => by rw [hTT, hmm]
  rw [e1, e2]
  exact key

theorem sum_exponent {r : ℕ} (c : Composition (r + 1)) : ∀ n, n ≤ c.length →
    ∑ b ∈ univ.filter (fun b : Fin c.length => b.1 < n),
      (2 * r + 1 + c.blocksFun b - 2 * c.sizeUpTo (b.1 + 1)) * c.blocksFun b =
      c.sizeUpTo n * (2 * r + 1 - c.sizeUpTo n) := by
  intro n hn
  induction n with
  | zero => simp
  | succ n ih =>
    have hn' : n < c.length := by omega
    rw [filter_lt_succ hn', Finset.sum_insert (by simp), ih (by omega)]
    have hs := c.sizeUpTo_succ' ⟨n, hn'⟩
    have hle := c.sizeUpTo_le (n + 1)
    have hpos := c.one_le_blocksFun ⟨n, hn'⟩
    simp only at hs
    rw [hs] at hle ⊢
    generalize c.sizeUpTo n = x at hle ⊢
    generalize c.blocksFun ⟨n, hn'⟩ = y at hle hpos ⊢
    have h1 : x ≤ 2 * r + 1 := by omega
    have h2 : 2 * (x + y) ≤ 2 * r + 1 + y := by omega
    have h3 : x + y ≤ 2 * r + 1 := by omega
    zify [h1, h2, h3]
    ring

theorem endMin_sq {E : Type} [Field E] {r : ℕ} (rd : ℝ) (γ : PN.Pts E r) (a : Fin γ.1.length)
    (v : InfinitePlace E) :
    (rd ^ (2 * (endIdx γ a * (2 * r + 1 - endIdx γ a))))⁻¹ * v (endMin γ a) ^ 2 =
      ∏ b ∈ univ.filter (fun b : Fin γ.1.length => b ≤ a),
        ((rd ^ (2 * r + 1 + γ.1.blocksFun b - 2 * endIdx γ b))⁻¹ * v (γ.2 b)) ^ (2 * γ.1.blocksFun b) := by
  have ha := a.2
  have hsum := sum_exponent γ.1 (a.1 + 1) (by omega)
  rw [← filter_le_eq] at hsum
  unfold endIdx
  have hrd : ∏ b ∈ univ.filter (fun b : Fin γ.1.length => b ≤ a),
      ((rd ^ (2 * r + 1 + γ.1.blocksFun b - 2 * γ.1.sizeUpTo (b.1 + 1)))⁻¹) ^ (2 * γ.1.blocksFun b) =
      (rd ^ (2 * (γ.1.sizeUpTo (a.1 + 1) * (2 * r + 1 - γ.1.sizeUpTo (a.1 + 1)))))⁻¹ := by
    simp_rw [inv_pow, ← pow_mul]
    rw [Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum, ← hsum, Finset.mul_sum]
    congr 2
    exact Finset.sum_congr rfl fun b _ => by ring
  have hmin : v (endMin γ a) ^ 2 = ∏ b ∈ univ.filter (fun b : Fin γ.1.length => b ≤ a),
      v (γ.2 b) ^ (2 * γ.1.blocksFun b) := by
    unfold endMin Formalism.HermitianLatticeCounting.ExpansionTerms.IndexedMinorEntry
    rw [map_prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [map_mul, map_pow]
    have hsg : v (((Formalism.HermitianLatticeCounting.ExpansionTerms.ParitySign (γ.1.blocksFun b) : ℤ) : E)) = 1 := by
      rw [Formalism.HermitianLatticeCounting.ExpansionTerms.ParitySign]
      push_cast
      rw [map_pow]
      have hm1 : v (-1) = 1 := by
        have h1 : v (-1) * v (-1) = 1 := by rw [← map_mul, neg_one_mul, neg_neg, map_one]
        have h0 : 0 ≤ v (-1) := by
          first
            | exact v.1.nonneg (-1)
            | exact apply_nonneg v (-1)
            | positivity
        nlinarith
      rw [hm1, one_pow]
    rw [hsg, one_mul, ← pow_mul, mul_comm]
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib, hrd, hmin]

theorem gram_pow_le_haar : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (r k TT : ℕ) (rd H : ℝ) (γ : PN.Pts E r), 0 < rd → (∀ a, 1 ≤ ∏ v : InfinitePlace E, (rd ^ (2 * (endIdx γ a * (2 * r + 1 - endIdx γ a))))⁻¹ * v (endMin γ a) ^ 2) → NDPt rd γ ≤ H → NGPt rd TT γ ^ (k - 1) ≤ H ^ (6 * (2 * r + 2)) * nPt rd k TT γ := by
  intro E _ _ _ r k TT rd H γ hrd hN hD
  have hw0 : ∀ (w : InfinitePlace E) (x : E), 0 ≤ w x := fun w x => by
    first
      | exact w.1.nonneg x
      | exact apply_nonneg w x
      | positivity
  let Tw : Fin γ.1.length → InfinitePlace E → ℝ := fun a w =>
    (rd ^ (2 * r + 1 + γ.1.blocksFun a - 2 * endIdx γ a))⁻¹ * w (γ.2 a)
  let U : Fin γ.1.length → ℝ := fun a => ∏ w : InfinitePlace E, Tw a w ^ (2 * γ.1.blocksFun a)
  let mm : Fin γ.1.length → ℕ := fun a => 2 * (r + 1 - endIdx γ a) + γ.1.blocksFun a - 1
  have hTw : ∀ a w, 0 ≤ Tw a w := fun a w => mul_nonneg (inv_nonneg.2 (pow_nonneg hrd.le _)) (hw0 _ _)
  have hU : ∀ a, 0 ≤ U a := fun a => Finset.prod_nonneg fun w _ => pow_nonneg (hTw a w) _
  have hNa : ∀ a, ∏ b ∈ univ.filter (fun b : Fin γ.1.length => b ≤ a), U b =
      ∏ w : InfinitePlace E, (rd ^ (2 * (endIdx γ a * (2 * r + 1 - endIdx γ a))))⁻¹ * w (endMin γ a) ^ 2 := by
    intro a
    simp only [U]
    rw [Finset.prod_comm]
    exact Finset.prod_congr rfl fun w _ => (endMin_sq rd γ a w).symm
  have hmM : ∀ a, mm a ≤ 6 * (2 * r + 2) := by
    intro a
    simp only [mm]
    have h1 := γ.1.sizeUpTo_le (a.1 + 1)
    have h2 := γ.1.sizeUpTo_succ' a
    unfold endIdx
    omega
  have key := one_le_partial U mm (6 * (2 * r + 2)) (fun a => by rw [hNa]; exact hN a) hU hmM
  have hND : (∏ a : Fin γ.1.length, ∏ b ∈ univ.filter (fun b : Fin γ.1.length => b ≤ a), U b) =
      NDPt rd γ := by
    unfold NDPt
    exact Finset.prod_congr rfl fun a _ => hNa a
  rw [hND] at key
  have hNDnn : 0 ≤ NDPt rd γ := Finset.prod_nonneg fun a _ => Finset.prod_nonneg fun w _ =>
    mul_nonneg (inv_nonneg.2 (pow_nonneg hrd.le _)) (pow_nonneg (hw0 _ _) _)
  have hY : ∏ a, U a ^ mm a = ∏ w : InfinitePlace E, ∏ a : Fin γ.1.length,
      Tw a w ^ (2 * γ.1.blocksFun a * (2 * (r + 1 - endIdx γ a) + γ.1.blocksFun a - 1)) := by
    simp only [U, mm]
    simp_rw [← Finset.prod_pow, ← pow_mul]
    rw [Finset.prod_comm]
  have hn : nPt rd k TT γ = NGPt rd TT γ ^ (k - 1) * ∏ a, U a ^ mm a := by
    rw [hY]
    unfold nPt NGPt
    rw [Finset.prod_mul_distrib, Finset.prod_pow]
  have hG0 : 0 ≤ NGPt rd TT γ := Finset.prod_nonneg fun w _ =>
    mul_nonneg (inv_nonneg.2 (pow_nonneg hrd.le _)) (hw0 _ _)
  have hYnn : 0 ≤ ∏ a, U a ^ mm a := Finset.prod_nonneg fun a _ => pow_nonneg (hU a) _
  have h1 : 1 ≤ H ^ (6 * (2 * r + 2)) * ∏ a, U a ^ mm a :=
    calc 1 ≤ NDPt rd γ ^ (6 * (2 * r + 2)) * ∏ a, U a ^ mm a := key
      _ ≤ H ^ (6 * (2 * r + 2)) * ∏ a, U a ^ mm a :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hNDnn hD _) hYnn
  rw [hn]
  calc NGPt rd TT γ ^ (k - 1) = NGPt rd TT γ ^ (k - 1) * 1 := (mul_one _).symm
    _ ≤ NGPt rd TT γ ^ (k - 1) * (H ^ (6 * (2 * r + 2)) * ∏ a, U a ^ mm a) :=
      mul_le_mul_of_nonneg_left h1 (pow_nonneg hG0 _)
    _ = H ^ (6 * (2 * r + 2)) * (NGPt rd TT γ ^ (k - 1) * ∏ a, U a ^ mm a) := by ring

end GlobalTheory.HaarWeight
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramInvariantPowLeHaarWeightStatement
open NumberField Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_invariant_pow_le_haar_weight : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (r k TT : ℕ) (rd H : ℝ) (γ : PN.Pts E r), 0 < rd → (∀ a, 1 ≤ ∏ v : InfinitePlace E, (rd ^ (2 * (endIdx γ a * (2 * r + 1 - endIdx γ a))))⁻¹ * v (endMin γ a) ^ 2) → NDPt rd γ ≤ H → NGPt rd TT γ ^ (k - 1) ≤ H ^ (6 * (2 * r + 2)) * nPt rd k TT γ := by
  first | exact @GlobalTheory.HaarWeight.gram_pow_le_haar | exact GlobalTheory.HaarWeight.gram_pow_le_haar | (intros; apply GlobalTheory.HaarWeight.gram_pow_le_haar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyGenericMassPositiveBoundedProof
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt Formalism.L2.SG.NGData Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.WeightsFamPf

theorem weightsFam_of (hS : PI.VolStabS.MassDataS.SWXS) : GlobalTheory.SnFam.WeightsFam := by
  intro Cg cb Cw cT CT C0
  obtain ⟨aH, bH, hH⟩ := GlobalTheory.T.differentLocalIdentity_familiesLemmaH Cg cb Cw cT CT C0
  refine ⟨max aH 2, bH, fun C' Cl e1 e2 D large₂ X Y u u' hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire _hBk
    K S TS cls hFQ γ _hγ Fm hFT _hRel _hTerm hG5 => ?_⟩
  have hC' : (2 : ℝ) ≤ C' := le_trans (le_max_right _ _) e1
  have hCH : aH ≤ C' := le_trans (le_max_left _ _) e1

  have hk4 : 4 * D.R.rS + 7 ≤ D.R.k := four_rank_add_seven_le_k hc
  have hk5 : 2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k := by
    obtain ⟨⟨hH0, _, _⟩, _, _⟩ := hc
    unfold Formalism.MainNotions.S.StandingHypotheses at hH0
    dsimp only at hH0
    obtain ⟨-, h2, h3, -, -⟩ := hH0
    have hm2 := D.R.two_le_m
    obtain ⟨j, hj⟩ := D.R.m_even
    have hmr : 2 * D.R.rS + 2 = D.R.m := by simp only [Formalism.BasicNotions.Ranks.rS]; omega
    have hL : (1 : ℝ) ≤ large₂.sc.L := Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
    have hm : (2 : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast hm2
    have hf : ((D.R.m : ℝ)) ^ 4 ≤ (D.R.f : ℝ) := by exact_mod_cast h3
    have hm5 : (2 : ℝ) ^ 5 ≤ (D.R.m : ℝ) ^ 5 := pow_le_pow_left₀ (by norm_num) hm 5
    have hm4 : (2 : ℝ) ^ 4 ≤ (D.R.m : ℝ) ^ 4 := pow_le_pow_left₀ (by norm_num) hm 4
    have hmm : (D.R.m : ℝ) ≤ (D.R.m : ℝ) ^ 4 := by
      have h1 : (1 : ℝ) ≤ (D.R.m : ℝ) := by linarith
      calc (D.R.m : ℝ) = (D.R.m : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (D.R.m : ℝ) ^ 4 := pow_le_pow_right₀ h1 (by norm_num)
    have hf0 : (0 : ℝ) ≤ (D.R.f : ℝ) := by positivity
    have h64 : (64 : ℝ) ≤ C' * (D.R.m : ℝ) ^ 5 := by nlinarith
    have ha : 64 * (D.R.f : ℝ) ≤ C' * (D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) := mul_le_mul_of_nonneg_right h64 hf0
    have hb' : C' * (D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) ≤ C' * (D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) * large₂.sc.L :=
      le_mul_of_one_le_right (by nlinarith) hL
    have hreal : (D.R.m : ℝ) + (D.R.f : ℝ) + 5 ≤ (D.R.k : ℝ) := by nlinarith
    have hnat : D.R.m + D.R.f + 5 ≤ D.R.k := by exact_mod_cast hreal
    omega

  have hLaw := GlobalTheory.T.matchedFamily_mass_law_base_situation Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc K S TS cls hFQ γ Fm hFT hG5
  obtain ⟨_w0, F, F', _Y0, _hw0, _hn, _hZ, _hTP, hBase, _hML, _hgenL⟩ := id hLaw
  have hcong := GlobalTheory.T.flagNorms_congr_mod_level_sq D (zOf Y) Fm.FP u u' F F' hBase.1 (fun p => (hBase.2.1 p).2.2.2.2.2.2)

  obtain ⟨hpos, hHp, w, G', hw, hzt, hTP', hcell, hglue⟩ := GlobalTheory.T.genericMass_le_heightPow_mul_gluedCount D X Y u u' hk4 Fm γ hG5.1 hLaw
  obtain ⟨-, -, -, -, -, -, ⟨_, _, -, -, -, -, -, hLT⟩, -⟩ := hc.2.2
  obtain ⟨s, hgl, hs⟩ := GlobalTheory.T.gluedLattice_weightedCount_le_explicit D X Y u u' hLT hk5 hcong G' hzt hTP'
  obtain ⟨hne, hngen⟩ := hglue s hgl
  obtain ⟨⟨Λ, hΛ, hEZ⟩, hgs⟩ := hs hne
  obtain ⟨hfac, hAA⟩ := GlobalTheory.T.meanCountConstant_eq_unscaledMainConstant hS Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc hk5 hcong hb X0 ψ hT sd C Th F0 what₂
    vR Q i0 i0' νq
  obtain ⟨hDl, hNG, hLam⟩ := GlobalTheory.T.norms_invariants_generic_rational_framePair D X Y u u' hcong G' Λ w hzt hTP' hΛ hEZ hcell
  have hHT := hH C' Cl hCH e2 D large₂ X Y u u' hc TS cls (nmlOf Y u u') γ Fm hFT
  subst hw
  have hrd : 0 < D.host.rdE := by
    unfold Host.rdE
    apply Real.rpow_pos_of_pos
    exact abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero _)
  set HP := HPt D.host.rdE (X.B.g : ℝ) ((Tu D u : ℕ) * (Tu D u' : ℕ)) (toPts w) with hHPdef
  have hHt1 : 1 ≤ Fm.toL.Htot := by
    show 1 ≤ ∏ p : {p // p ∈ Fm.P}, (Fm.FP p.1).Hp
    have := Finset.prod_le_prod₀ (s := Finset.univ) (f := fun _ : {p // p ∈ Fm.P} => (1 : ℝ))
      (g := fun p => (Fm.FP p.1).Hp) (fun _ _ => zero_le_one) (fun p _ => hHp p.1 p.2)
    simpa using this
  have hH1 : 1 ≤ HP := by rw [hHT]; exact hHt1
  have hg1 : (1 : ℝ) ≤ (X.B.g : ℝ) := by
    obtain ⟨-, -, -, -, -, -, -, hg0, hg1, -⟩ := hc.2.1
    rw [X.g_eq]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hg0.ne_zero hg1.ne_zero)
  have hgS : ((gS D : ℕ) : ℝ) = (X.B.g : ℝ) := by rw [X.g_eq]; rfl
  have hND0 : 0 ≤ NDPt D.host.rdE (toPts w) := by
    unfold NDPt
    exact Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => by positivity
  have hND : NDPt D.host.rdE (toPts w) ≤ HP := by
    have h1 : 1 ≤ ((X.B.g : ℝ) ^ ((2 * D.R.rS + 1) * Fintype.card (InfinitePlace D.host.E)))⁻¹ *
        NGPt D.host.rdE (Tu D u * Tu D u') (toPts w) := by
      have hp : 0 < (X.B.g : ℝ) ^ ((2 * D.R.rS + 1) * Fintype.card (InfinitePlace D.host.E)) :=
        pow_pos (by linarith) _
      rw [inv_mul_eq_div, le_div_iff₀ hp, one_mul]
      calc _ ≤ (X.B.g : ℝ) ^ ((2 * D.R.rS + 2) * Fintype.card (InfinitePlace D.host.E)) :=
            pow_le_pow_right₀ hg1 (Nat.mul_le_mul_right _ (by omega))
        _ ≤ _ := hgS ▸ hNG
    rw [hHPdef]
    unfold HPt
    exact le_mul_of_one_le_left hND0 h1
  have hhaar := GlobalTheory.T.gram_invariant_pow_le_haar_weight D.host.E D.R.rS D.R.k (Tu D u * Tu D u') D.host.rdE HP (toPts w) hrd hDl hND
  rw [← hHT] at hngen
  have hY0 : 0 ≤ NGPt D.host.rdE (Tu D u * Tu D u') (toPts w) ^ (D.R.k - 1) := by
    apply pow_nonneg
    exact le_trans (pow_nonneg (by positivity) _) hNG
  have hHa : 0 < HP ^ (3 * (D.R.rS + 1) ^ 2) := pow_pos (by linarith) _
  have hNle : Fm.toL.ngenTot ≤ HP ^ (3 * (D.R.rS + 1) ^ 2) *
      (2 * (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).AA * PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f) *
      NGPt D.host.rdE (Tu D u * Tu D u') (toPts w) ^ (D.R.k - 1) := by
    calc Fm.toL.ngenTot ≤ _ := hngen
      _ ≤ HP ^ (3 * (D.R.rS + 1) ^ 2) * (2 * ((bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).AA *
          Formalism.L2.SG.MassDataConc.ngFac D) * Formalism.L2.SG.CntLocal.sqrtAbsNormOfScaledGram ((Tu D u : ℕ) : D.host.E) ((Tu D u' : ℕ) : D.host.E)
            (ZhatL (lf D (X.Fu u)) G') ^ (D.R.k - 1)) := by
          rw [← hAA]; exact mul_le_mul_of_nonneg_left hgs hHa.le
      _ = _ := by rw [← mul_assoc 2, mul_assoc (2 * _), mul_comm (Formalism.L2.SG.MassDataConc.ngFac D), hLam]; ring
  have hc0 : 0 ≤ 2 * (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).AA *
      PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f := by
    by_contra hneg
    push_neg at hneg
    have h1 : HP ^ (3 * (D.R.rS + 1) ^ 2) * (2 * (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).AA *
        PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hHa.le hneg.le
    have h2 := mul_nonpos_of_nonpos_of_nonneg h1 hY0
    linarith
  have hnP : 0 ≤ nPt D.host.rdE D.R.k ((Tu D u : ℕ) * (Tu D u' : ℕ)) (toPts w) := by
    unfold nPt
    exact Finset.prod_nonneg fun _ _ => mul_nonneg (pow_nonneg (by positivity) _)
      (Finset.prod_nonneg fun _ _ => pow_nonneg (by positivity) _)
  have hab : 3 * (D.R.rS + 1) ^ 2 + 6 * (2 * D.R.rS + 2) ≤ PN.eN D.R.rS := by
    unfold PN.eN
    generalize (D.R.rS + 1) ^ 2 = t
    omega
  refine ⟨hpos, ?_⟩
  calc Fm.toL.ngenTot ≤ _ := hNle
    _ ≤ HP ^ (3 * (D.R.rS + 1) ^ 2) * (2 * (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).AA *
        PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f) * (HP ^ (6 * (2 * D.R.rS + 2)) *
          nPt D.host.rdE D.R.k (Tu D u * Tu D u') (toPts w)) :=
        mul_le_mul_of_nonneg_left hhaar (mul_nonneg hHa.le hc0)
    _ = (2 * (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).AA * PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f) *
        HP ^ (3 * (D.R.rS + 1) ^ 2 + 6 * (2 * D.R.rS + 2)) *
          nPt D.host.rdE D.R.k (Tu D u * Tu D u') (toPts w) := by ring
    _ ≤ (2 * (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).AA * PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f) *
        HP ^ PN.eN D.R.rS * nPt D.host.rdE D.R.k (Tu D u * Tu D u') (toPts w) := by
        gcongr
    _ = _ := by ring

end GlobalTheory.WeightsFamPf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyGenericMassPositiveBoundedProofStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt Formalism.L2.SG.NGData Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.familyGenericMassPositiveBounded_proof : PI.VolStabS.MassDataS.SWXS → GlobalTheory.SnFam.WeightsFam := by
  first | exact @GlobalTheory.WeightsFamPf.weightsFam_of | exact GlobalTheory.WeightsFamPf.weightsFam_of | (intros; apply GlobalTheory.WeightsFamPf.weightsFam_of <;> assumption)
end
