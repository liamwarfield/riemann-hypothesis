module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyJSZ
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LatBAsm
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.ChartCG
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcAllC
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.RealBracketOfRowBlock
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.CutLeavesDeepOutright
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierXVIndepP
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KFinDensePf

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpValAll
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets
  Formalism.L2.SG.MassDataConc Formalism.L2.SG.MassDataForm Formalism.L2.SG.Pf.RowForm MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem poincareConstant_pos {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u : D.what₂.Word) :
    0 < Formalism.L2.SG.PoincareInHH.PoincareSetting.c0X X u (Y.FN u) := by
  have hv := Formalism.L2.SG.Closed.VolPosC_holds D X Y u (Formalism.L2.SG.Closed.level_subgroup_properties X)
  haveI : Nontrivial (X.Vpi u) := Formalism.L2.SG.Pf.ColDictPf.vpi_nontrivial X u
  have hr : (0 : ℝ) < (Module.finrank ℂ (X.Vpi u) : ℝ) := by exact_mod_cast Module.finrank_pos
  rw [Formalism.L2.SG.Full.Full.poincare_constant_eq]
  exact div_pos (mul_pos hv.1 hv.2) hr

theorem amplitude_lower_bound_real {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
    (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (hSt : Formalism.MainNotions.S.Cnt.Stand D u u') (hi : ∀ v, i0 v = i0' v) (hNuP : Formalism.L2.SG.RealObj.NuQPin X u u' νq)
    (hVP : Formalism.L2.SG.VolPin.VolumeOddGeneric) (hg3 : ∀ i, 3 ≤ D.host.g i) :
    Formalism.L2.SG.Pf.RowForm.ClassAbs.AmpValLowerC X Y u u'
      (Formalism.L2.SG.PairVal.vRdef D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M) i0 i0' νq := by
  have hPH : Formalism.MainNotions.S.Lat.PrimeHyp D u (Formalism.MainNotions.S.Lat.Tu D u') := Formalism.MainNotions.VanishingOnXAndXPlus.primeHyp_of_stand D u u' hSt
  have hi' : i0' = i0 := funext fun v => (hi v).symm
  subst hi'
  let κ : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℕ := fun _ => 0
  have hAtS : ∀ t : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u), t.G ≠ 0 → t.relevant → ∃ w, t.atPt w :=
    fun t hG hr => Formalism.L2.SG.LeadingMinorsNonvanishing.atSomeAll_holds D X Y u u' t hG hr
  have hCU : Formalism.L2.SG.PairVal.CellPtUnique D u u' (X.Fu u) (Y.what₂ u) :=
    Formalism.L2.SG.Pf.cell_point_unique_of_term_fun (Formalism.L2.SG.Closed.TermFun_holds D u u') (Y.rowsOK u)
  have hNR : Formalism.L2.SG.PairVal.NormRepExists D u u' (X.Fu u) (Y.what₂ u) :=
    Formalism.L2.SG.Pf.normRepExists_of (Formalism.L2.SG.Pf.NormRepX.norm_representative_holds D u u' hPH)
      (Formalism.L2.SG.Closed.TermFun_holds D u u') (Y.rowsOK u)
  have hLD : Formalism.L2.SG.Pf.RowForm.LiftDecompC X Y u u' κ :=
    Formalism.L2.SG.Pf.RowForm.liftDecompC_of_real (κ := κ) (h := Formalism.L2.SG.Pf.RowForm.RealDecompL.realDecompC_of (hAt := hAtS))
  have hFT := Formalism.L2.SG.Pf.formula_transport_of_condition (κ := κ) (hP := hNuP) (hV := hVP) (hg3 := hg3) (hPH := hPH)
    (hRC := Formalism.L2.SG.Pf.RelChar.relCharC_holds) (hLD := hLD) (hAt := Formalism.L2.SG.Pf.LiftedPhaseAgreement.liftAtSomeC_holds X Y u u' κ)
    (hNR := hNR) (hCPU := hCU)
  have hDF : Formalism.L2.SG.Pf.RowForm.DFrameAtS X u u' i0' i0' 1 := Formalism.L2.SG.Pf.Carrier.dual_frame_at_places X u u' 1 i0'
  have hNF := Formalism.L2.SG.Pf.RowForm.normalFormC_all (hAtS := hAtS) (hTP := fun t w h => Formalism.L2.SG.WConst.atPt_totPos t w h)
    (hCU := hCU) (hDF := hDF) (hPT := Formalism.L2.SG.Pf.LiftedPhaseAgreement.phaseTieC_holds (κ := κ) (hP := hPH)) (hFT := hFT)
  refine Formalism.L2.SG.Pf.ampValLowerC_of X Y u u' _ i0' i0' νq κ hNF
    (fun t w h => Formalism.L2.SG.Pf.FinXP.atPtRelevant_holds D u u' _ _ t w h) ?_
  have hK := Formalism.L2.SG.Closed.level_subgroup_properties X
  have hV : 0 < X.volK2 := by
    unfold Formalism.L2.SG.HidaSetting.HidaSetting.volK2
    exact ENNReal.toReal_pos hK.2.2.1.ne' hK.2.2.2.ne
  have hc := poincareConstant_pos X Y u
  have hc' := poincareConstant_pos X Y u'
  unfold Formalism.L2.SG.TermOp.scl
  exact mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr (mul_pos hc hc'))) hV

end Formalism.L2.SG.Pf

namespace Formalism.L2.SG.PoincareAmplitudeLowerBounds

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.SpectralTiesReal Formalism.L2.SG.RowsConc Formalism.L2.SG.RealObj

theorem rowsSum_of_formula_volume (hFC : FormulaC) (hVP : Formalism.L2.SG.VolPin.VolumeOddGeneric) : RowsSumC := by
  intro D T u u' i0 i0' νq Lsp κ hne hSt hCT hg3 hk hcong hi hPR hNu hRL
  have hWD : Formalism.L2.SG.WuDecay.WuDecay T.X := hCT.2.2.2.2.1
  have hAbs : (T.Y.tO u u').AbsConv :=
    Formalism.L2.SG.Pf.absConvC_outright D T.X T.Y u u'
      (Formalism.L2.SG.Closed.FoldOKC_outright D T.X T.Y u (Formalism.L2.SG.Closed.level_subgroup_properties T.X) hWD)
      (Formalism.L2.SG.Closed.FoldOKC_outright D T.X T.Y u' (Formalism.L2.SG.Closed.level_subgroup_properties T.X) hWD)
      (Formalism.L2.SG.Pf.fundExistsC_holds D T.X T.Y u u')
      (Formalism.L2.SG.Pf.KernelOfEmbedding.ooIntAll_of (Y := T.Y) hWD u u')
  have hL := Formalism.L2.SG.Pf.liftOntoC_of (fun D => Formalism.L2.SG.Pf.WittFlags.LatIso_holds D) D T.X T.Y u u'
  have hAF : Formalism.L2.SG.PairVal.AutFin D (T.X.Fu u) (T.Y.what₂ u) := fun Λ hΛ =>
    _root_.automorphism_lattice_finite D (D.sp.Y_sig 0) _ (D.mem u).A.T_prime.pos (T.X.Fu u) Λ ((T.Y.rowsOK u).1 Λ hΛ)
  have hAF' : Formalism.L2.SG.PairVal.AutFin D (T.X.Fu u') (T.Y.what₂ u') := fun Λ hΛ =>
    _root_.automorphism_lattice_finite D (D.sp.Y_sig 0) _ (D.mem u').A.T_prime.pos (T.X.Fu u') Λ ((T.Y.rowsOK u').1 Λ hΛ)
  have hLT : Formalism.L2.SG.Pf.LocCP.LocTied D := by
    obtain ⟨_, _, _, _, _, _, _, hL⟩ := hCT.2.2.2.2.2.2.1
    exact hL
  have hnc : 0 < Formalism.L2.SG.Pf.Cnt.cExpl D (T.X.Fu u) (T.Y.what₂ u) * ∏' p, Formalism.L2.SG.DataInst.alpD u u' p :=
    mul_pos (hFC D T u u' Lsp hLT hSt hcong).1 (tprod_alpD_pos D hk u u')
  exact Formalism.L2.SG.RowsAbsX.rowsSum_of_val _ κ _ i0 i0' (T.Y.FN u) (T.Y.FN u') νq hAbs hL
    (Formalism.L2.SG.Pf.amplitude_lower_bound_real T.X T.Y u u' i0 i0' νq hSt hi hNu hVP hg3) hAF hAF' hnc

end Formalism.L2.SG.PoincareAmplitudeLowerBounds
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXDens
noncomputable section

open scoped Classical
open ValuativeRel

namespace Formalism.L2.SG.Pf.MassDataX

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.DataInst Formalism.L2.SG.CntLocal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem one_sub_eta_nonneg (η : ℝ) (hη : η = 1 ∨ η = -1) (q i : ℕ) : 0 ≤ 1 - η ^ i / ((q : ℕ) : ℝ) ^ i := by
  have h1 : |η ^ i| = 1 := by
    rcases hη with rfl | rfl <;> simp [abs_pow]
  rcases Nat.eq_zero_or_pos (q ^ i) with h | h
  · have h' : ((q : ℕ) : ℝ) ^ i = 0 := by exact_mod_cast h
    rw [h', div_zero]
    norm_num
  · have h' : (1 : ℝ) ≤ ((q : ℕ) : ℝ) ^ i := by exact_mod_cast (show 1 ≤ q ^ i from h)
    have h2 : η ^ i / ((q : ℕ) : ℝ) ^ i ≤ 1 := by
      rw [div_le_one (by linarith)]
      exact (le_abs_self _).trans (h1.le.trans h')
    linarith

theorem etaP_pm {D : D7} (p : PlF D) : eta₃ p = 1 ∨ eta₃ p = -1 := by
  unfold eta₃
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem aPD_nonneg {D : D7} (p : PlF D) (T : ℕ) : 0 ≤ aPD p T := by
  unfold aPD
  apply Finset.prod_nonneg
  intro i _
  exact one_sub_eta_nonneg _ (etaP_pm p) _ _

theorem alpD_nonneg {D : D7} (u u' : D.what₂.Word) (p : PlF D) : 0 ≤ alpD u u' p := by
  unfold alpD
  split_ifs
  · exact aPD_nonneg p _
  · exact mul_nonneg (aPD_nonneg p _) (aPD_nonneg p _)

theorem densP_nonneg {D : D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (L : LocSp D M)
    (δ : ∀ p : PlF D, (D.s.atP p).Fp) (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]) (T T' : D.host.E) (Z : MatZ D) (p : PlF D) :
    0 ≤ densP L δ ϖ T T' Z p := by
  unfold densP Formalism.MainNotions.S.Loc.HermSp.dens
  positivity

theorem densNonnegAll_holds : Formalism.L2.SG.PoincareAmplitudeLowerBounds.DensNonnegAll := by
  intro D T u u' Lsp ϖ
  apply div_nonneg
  · unfold supDens
    apply Real.sSup_nonneg
    intro d hd
    simp only [densSet, Set.mem_setOf_eq] at hd
    obtain ⟨Z, -, rfl⟩ := hd
    exact tprod_nonneg fun p => densP_nonneg _ _ _ _ _ _ _
  · exact tprod_nonneg fun p => alpD_nonneg u u' p

end Formalism.L2.SG.Pf.MassDataX
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NormalizingConstantPositiveAll
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.NcAllC

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.LocVol
  Formalism.L2.SG.MassDataConc Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Formalism.L2.SG.PoincareAmplitudeLowerBounds
  Formalism.L2.SG.DataInst Formalism.L2.SG.CntLocal NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 4000000 in
variable [Fact PI.AprimeInfW.GaugeVolUD] [Fact Formalism.L2.SG.Pf.WB.RhsWLim] [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem normalizing_constants_all (hCov : Formalism.L2.SG.Pf.NcReal.JX.CovolRef) (hSW : PI.VolStabS.MassDataS.SWXS) : NormalizingConstantPositiveAll := by
  intro D T u u' X0 C Th Q i0 i0' νq Lsp ϖ hne hSt hCT hdet hk hcong hi hPR hNu hϖ
  have hK2 := Formalism.L2.SG.Closed.level_subgroup_properties T.X
  have hV : 0 < T.X.volK2 := ENNReal.toReal_pos (ne_of_gt hK2.2.2.1) (ne_of_lt hK2.2.2.2)
  have hH : Formalism.L2.SG.TypedSets.HypX T.X T.hb (T.Y.FN u) (T.Y.FN u') u u' :=
    ⟨T.measTie, hCT.1, T.Y.FN_fund u, T.Y.FN_fund u'⟩
  have hStd : StdHyp T.X.B.I.cm.sig T.X.B.I.J T.ψ :=
    ⟨MassDataVolumesW.stepCM T.X, MassDataVolumesW.stepHerm T.X, T.ψ_char, T.ψ_std⟩
  have hlat : ∃ L : Submodule (NumberField.RingOfIntegers T.X.B.I.E) (Fin T.X.B.I.n → T.X.B.I.E),
      Submodule.IsFullLattice T.X.B.I.E L ∧
      (L : Set (Fin T.X.B.I.n → T.X.B.I.E)) = (T.X.B.I.L : Set (Fin T.X.B.I.n → T.X.B.I.E)) :=
    ⟨T.X.B.I.L, ⟨{ toIsLattice := Submodule.IsLattice.of_fg T.X.B.I.E T.X.B.I.L_fg,
                    span_eq_top := T.X.B.I.L_span }, rfl⟩⟩
  have hdet' : (gramE T.X.B.I.cm.sig T.X.B.I.J (tupH (frameOf T.X u'))).det ≠ 0 :=
    Formalism.L2.SG.Pf.Rescale.standard_gram_nondegenerate T.X.B.I.F T.X.B.I.E T.X.B.I.cm.sig T.X.B.I.n T.X.B.I.J _ _ _
      (fun x => star_star x) hStd.2.1 (Formalism.L2.SG.Pf.Rescale.frame_stdX T.X u')
  have hPC := Formalism.L2.SG.Pf.ProdConvCut2.prodConvAll_holds D T u u' hne hSt
  have hL := locTieX_of T.X T.ψ u (T.locCompat u) (Formalism.L2.SG.Pf.LocVolPrim.primX T.X u locFramePrim)
  have hL' := locTieX_of T.X T.ψ u' (T.locCompat u') (Formalism.L2.SG.Pf.LocVolPrim.primX T.X u' locFramePrim)
  have hTF := Formalism.L2.SG.Pf.typFacts_holds T.X T.hb u u'
  have hsd := Formalism.L2.SG.Pf.MassDataX.densNonnegAll_holds D T u u' Lsp ϖ
  have hQ := Formalism.L2.SG.Pf.MassDataPos.quotVolPosC_of T.X T.hb T.Y u u' X0 T.ψ (T.Y.tO u u')
    (supDens Lsp T.Y.δ ϖ u u' (T.X.Fu u) (T.Y.what₂ u) / ∏' p, alpD u u' p) 0 1
    (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) Q T.Y.M T.Y.δ i0 i0' νq hK2 hV
  have hN := ncTieC_of_closed T.X T.hb T.Y.hK (T.Y.FN u) (T.Y.FN u') u u' X0 T.ψ (T.Y.tO u u')
    (supDens Lsp T.Y.δ ϖ u u' (T.X.Fu u) (T.Y.what₂ u) / ∏' p, alpD u u' p) 0 1
    (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) Q T.Y.M T.Y.δ i0 i0' νq hCov hSW
    hH T.measCompat hStd hlat hdet' hdet hPC hL hL' hTF hQ hsd le_rfl one_pos hcong (T.Y.rowsOK u)
  have hc0 : 0 < (bCF T.X T.hb T.Y.hK (T.Y.FN u) (T.Y.FN u') u u' X0 T.ψ (T.Y.tO u u')
      (supDens Lsp T.Y.δ ϖ u u' (T.X.Fu u) (T.Y.what₂ u) / ∏' p, alpD u u' p) C Th
      (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) Q T.Y.M T.Y.δ i0 i0' νq).c0 := by
    have h := Formalism.L2.SG.Pf.poincareConstant_pos T.X T.Y u
    have e : Formalism.L2.SG.PoincareInHH.PoincareSetting.c0X T.X u (T.Y.FN u) = T.X.volK2 *
        ((T.X.muN u (T.Y.FN u)).toReal * (T.X.muH u Set.univ).toReal / (Module.finrank ℂ (T.X.Vpi u) : ℝ)) := by
      unfold Formalism.L2.SG.PoincareInHH.PoincareSetting.c0X; ring
    rw [e] at h
    exact pos_of_mul_pos_right h hV.le
  have hc0' : 0 < (bCF T.X T.hb T.Y.hK (T.Y.FN u) (T.Y.FN u') u u' X0 T.ψ (T.Y.tO u u')
      (supDens Lsp T.Y.δ ϖ u u' (T.X.Fu u) (T.Y.what₂ u) / ∏' p, alpD u u' p) C Th
      (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) Q T.Y.M T.Y.δ i0 i0' νq).c0' := by
    have h := Formalism.L2.SG.Pf.poincareConstant_pos T.X T.Y u'
    have e : Formalism.L2.SG.PoincareInHH.PoincareSetting.c0X T.X u' (T.Y.FN u') = T.X.volK2 *
        ((T.X.muN u' (T.Y.FN u')).toReal * (T.X.muH u' Set.univ).toReal / (Module.finrank ℂ (T.X.Vpi u') : ℝ)) := by
      unfold Formalism.L2.SG.PoincareInHH.PoincareSetting.c0X; ring
    rw [e] at h
    exact pos_of_mul_pos_right h hV.le
  exact ⟨hN, mul_pos hc0 hc0'⟩

end Formalism.L2.SG.Pf.NcAllC
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.VolumeDeterminedOfChart
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CovolOne3CHolds
namespace Formalism.L2.SG.NGCut.StabilizerCovolume

theorem covolOne3C_holds : Formalism.L2.SG.Pf.VolPinAsm.CovolOne3C :=
  covolOne3C_of Formalism.L2.S.Pv.Chart.chartC_holds (stabilizerLatticeCoordinates_of Formalism.L2.SG.LatBAsm.stabilizer_lattice_twisted_prod)

end Formalism.L2.SG.NGCut.StabilizerCovolume
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.VolIdxFinP
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfCong
noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.PairVal Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.PtCell Formalism.L2.SG.RealObj
  Formalism.L2.SG.Pf.BlockPermutation Formalism.L2.SG.Pf.StabIntSh Formalism.L2.SG.Pf.StabIntLat

namespace Formalism.L2.SG.Pf.StabIntCong

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem intE_iff (x : D.host.E) : Formalism.L2.SG.Pf.StabilizerIndexVolumes.IntE x ↔ x ∈ (1 : FI D) := by
  rw [FractionalIdeal.mem_one_iff]
  exact ⟨fun ⟨o, h⟩ => ⟨o, h⟩, fun ⟨o, h⟩ => ⟨o, h⟩⟩

theorem one_mem_one_FI : (1 : D.host.E) ∈ (1 : FI D) := (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩

theorem natCast_mem_one_FI (n : ℕ) : (n : D.host.E) ∈ (1 : FI D) := (FractionalIdeal.mem_one_iff _).2 ⟨n, map_natCast _ _⟩

theorem mul_mem_one_FI {x y : D.host.E} (hx : x ∈ (1 : FI D)) (hy : y ∈ (1 : FI D)) : x * y ∈ (1 : FI D) := by
  have := FractionalIdeal.mul_mem_mul hx hy; rwa [one_mul] at this

abbrev ddI (D : D7) : Ideal (𝓞 D.host.E) :=
  Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))

theorem ddS_eq : ddS D = (ddI D : FI D) := rfl

theorem ddS_pow_le_one (h : ℕ) : ddS D ^ h ≤ 1 := by
  rw [ddS_eq, ← FractionalIdeal.coeIdeal_pow]; exact FractionalIdeal.coeIdeal_le_one

theorem one_le_ddPow (h : ℕ) : (1 : FI D) ≤ ddPow D h := by
  unfold ddPow
  rw [zpow_neg, zpow_natCast]
  have := FractionalIdeal.inv_anti_mono (pow_ne_zero h (ddS_ne (D := D))) (ddS_pow_le_one (D := D) h)
  rwa [inv_one] at this

theorem mem_dd_of_int {h : ℕ} {x : D.host.E} (hx : x ∈ (1 : FI D)) : x ∈ ddPow D h := one_le_ddPow h hx

theorem mem_qd_of_qq {h : ℕ} {x : D.host.E} (hx : x ∈ (qq D : FI D)) : x ∈ qdPow D h := by
  unfold qdPow
  have := FractionalIdeal.mul_mem_mul hx (mem_dd_of_int (h := h) one_mem_one_FI)
  rwa [mul_one] at this

theorem mul_mem_qq {x y : D.host.E} (hx : x ∈ (1 : FI D)) (hy : y ∈ (qq D : FI D)) : x * y ∈ (qq D : FI D) := by
  have := FractionalIdeal.mul_mem_mul hx hy; rwa [one_mul] at this

theorem qq_le_one {x : D.host.E} (hx : x ∈ (qq D : FI D)) : x ∈ (1 : FI D) := FractionalIdeal.coeIdeal_le_one hx

theorem gS_mem_qqE (x : D.host.E) (hx : x ∈ (1 : FI D)) : ((gS D : ℕ) : D.host.E) * x ∈ (qq D : FI D) := by
  obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
  rw [FractionalIdeal.mem_coeIdeal]
  exact ⟨(gS D : ℕ) * o, Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _), by simp⟩

theorem conjF_mem_one_FI {x : D.host.E} (hx : x ∈ (1 : FI D)) : D.conjF x ∈ (1 : FI D) := by
  obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
  rw [FractionalIdeal.mem_one_iff]
  have hi : IsIntegral ℤ (D.conjF (algebraMap (𝓞 D.host.E) D.host.E o)) :=
    (RingOfIntegers.isIntegral_coe o).map (D.conjF.toRingHom.toIntAlgHom)
  exact ⟨⟨_, hi⟩, rfl⟩

theorem conj_mem_qq {x : D.host.E} (hx : x ∈ (qq D : FI D)) : D.conjF x ∈ (qq D : FI D) := by
  obtain ⟨o, ho, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 ho
  have ht : D.conjF (algebraMap (𝓞 D.host.E) D.host.E t) ∈ (1 : FI D) :=
    conjF_mem_one_FI ((FractionalIdeal.mem_one_iff _).2 ⟨t, rfl⟩)
  rw [map_mul, map_mul, map_natCast, map_natCast, mul_comm]
  exact gS_mem_qqE _ ht

theorem absNorm_mem_ideal : ((Ideal.absNorm (ddI D) : ℕ) : D.host.E) ∈ ddS D := by
  rw [ddS_eq, FractionalIdeal.mem_coeIdeal]
  exact ⟨_, Ideal.absNorm_mem (ddI D), map_natCast _ _⟩

theorem absNorm_ddI_ne_zero : Ideal.absNorm (ddI D) ≠ 0 := by
  rw [Ne, Ideal.absNorm_eq_zero_iff]
  intro h
  apply ddS_ne (D := D)
  rw [ddS_eq, h, FractionalIdeal.coeIdeal_bot]

theorem pow_mem_ddS (k : ℕ) : ((Ideal.absNorm (ddI D) : ℕ) : D.host.E) ^ k ∈ ddS D ^ k := by
  induction k with
  | zero => simp only [pow_zero]; exact one_mem_one_FI
  | succ k ih => rw [pow_succ, pow_succ]; exact FractionalIdeal.mul_mem_mul ih absNorm_mem_ideal

theorem clear_den (k : ℕ) {x : D.host.E} (hx : x ∈ ddPow D k) :
    ((Ideal.absNorm (ddI D) : ℕ) : D.host.E) ^ k * x ∈ (1 : FI D) := by
  have := FractionalIdeal.mul_mem_mul (pow_mem_ddS k) hx
  unfold ddPow at this
  rwa [← zpow_natCast, ← zpow_add₀ (ddS_ne (D := D)), add_neg_cancel, zpow_zero] at this

theorem aBddOf (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) :
    Formalism.L2.SG.Pf.StabilizerIndexVolumes.ABddOf D u u' F0 what₂ δ M := by
  intro _ _ hA t w F' L U _ _ _ _
  refine ⟨Ideal.absNorm (ddI D) ^ D.R.rS, pow_ne_zero _ absNorm_ddI_ne_zero, fun h hh i j => ?_⟩
  rw [intE_iff]
  have hS := (stabIntShape D δ M hA u u' w h).1 hh
  obtain ⟨hlo, b, hb, hW, hE⟩ := hS
  push_cast
  rcases lt_trichotomy j i with hji | rfl | hij
  · have hk : i.val - j.val ≤ D.R.rS := by have := i.isLt; omega
    rw [show ((Ideal.absNorm (ddI D) : ℕ) : D.host.E) ^ D.R.rS =
        ((Ideal.absNorm (ddI D) : ℕ) : D.host.E) ^ (D.R.rS - (i.val - j.val)) *
          ((Ideal.absNorm (ddI D) : ℕ) : D.host.E) ^ (i.val - j.val) by
        rw [← pow_add, Nat.sub_add_cancel hk], mul_assoc]
    exact mul_mem_one_FI (by rw [← Nat.cast_pow]; exact natCast_mem_one_FI _) (clear_den _ (hE i j hji).1)
  · rw [(hlo _ _).2 rfl, mul_one, ← Nat.cast_pow]; exact natCast_mem_one_FI _
  · rw [(hlo i j).1 hij, mul_zero]; exact FractionalIdeal.zero_mem _

abbrev Sint (D : D7) : Subring D.host.E := (integralClosure ℤ D.host.E).toSubring

theorem mem_Sint_iff (x : D.host.E) : x ∈ Sint D ↔ x ∈ (1 : FI D) := by
  rw [FractionalIdeal.mem_one_iff]
  constructor
  · intro h; exact ⟨⟨x, h⟩, rfl⟩
  · rintro ⟨o, rfl⟩; exact o.2

theorem sign_mem_one (a c : Fin (D.R.rS + 1)) : (sgm a c : D.host.E) ∈ (1 : FI D) := by
  rcases sgm_cases a c with e | e
  · rw [e]; exact one_mem_one_FI
  · rw [e]; exact (1 : FI D).coeToSubmodule.neg_mem one_mem_one_FI

theorem aCong (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) :
    Formalism.L2.SG.Pf.StabilizerIndexVolumes.ACong D u u' F0 what₂ δ M := by
  intro _ hA t w F' L U _ _ _ _
  refine ⟨gS D, fun h0 => gS_ne (D := D) (by rw [h0]; simp), fun a ha hc => ?_⟩
  obtain ⟨hlo, b, hb, hW⟩ := ha
  have hq : ∀ i j, (a : MatR D) i j - (1 : MatR D) i j ∈ (qq D : FI D) := by
    intro i j
    have h1 := (intE_iff _).1 (hc i j)
    have := gS_mem_qqE _ h1
    rwa [mul_div_cancel₀ _ gS_ne] at this
  rw [mem_stabInt_iff_X δ M hA u u' w a hlo hb hW]
  obtain ⟨-, hU, hB⟩ := X_of_st w hlo hb hW
  set X := (ptMat w)⁻¹ * (a : MatR D) * ptMat w with hXdef
  have hXe : ∀ c d, X c d - (1 : MatR D) c d ∈ (qq D : FI D) := by
    intro c d
    by_cases hs : blkOf w.1 c.val = blkOf w.1 d.val
    · have hcv : cv w c = cv w d := pval_eq_blk w c d hs
      have hone : (1 : MatR D) c d = (1 : MatR D) (pinv w c) (pinv w d) := by
        by_cases hcd : c = d
        · rw [hcd]; simp
        · have : pinv w c ≠ pinv w d := fun e => hcd (pinv_inj w e)
          rw [Matrix.one_apply_ne hcd, Matrix.one_apply_ne this]
      rw [hXdef, Formalism.L2.SG.Pf.BlockPermutation.conj_apply, hcv, mul_comm, ← mul_assoc, mul_inv_cancel₀ (cv_ne w d), one_mul, hone]
      exact hq _ _
    · have hcd : c ≠ d := fun e => hs (by rw [e])
      rw [hB c d hs, Matrix.one_apply_ne hcd, sub_zero]
      exact FractionalIdeal.zero_mem _
  have hX1 : ∀ c d, X c d ∈ (1 : FI D) := by
    intro c d
    have := (1 : FI D).coeToSubmodule.add_mem (qq_le_one (hXe c d))
      (show (1 : MatR D) c d ∈ (1 : FI D) by
        by_cases h : c = d
        · rw [h, Matrix.one_apply_eq]; exact one_mem_one_FI
        · rw [Matrix.one_apply_ne h]; exact FractionalIdeal.zero_mem _)
    rwa [sub_add_cancel] at this
  have hXi1 : ∀ c d, X⁻¹ c d ∈ (1 : FI D) := by
    have hL : StabIntGrp.LoIn (Sint D) X.transpose := by
      refine ⟨fun c => (hU c c).2 rfl, fun c d h => (hU d c).1 h, fun c d => (mem_Sint_iff _).2 (hX1 d c)⟩
    have := StabIntGrp.loIn_inv hL
    rw [← Matrix.transpose_nonsing_inv] at this
    intro c d
    exact (mem_Sint_iff _).1 (this.2.2 d c)
  have hXd : IsUnit X.det := by rw [upU_det hU]; exact isUnit_one
  have hXie : ∀ c d, X⁻¹ c d - (1 : MatR D) c d ∈ (qq D : FI D) := by
    have hm : X⁻¹ - 1 = -(X⁻¹ * (X - 1)) := by
      rw [Matrix.mul_sub, Matrix.nonsing_inv_mul _ hXd, Matrix.mul_one, neg_sub]
    intro c d
    rw [← Matrix.sub_apply, hm, Matrix.neg_apply, Matrix.mul_apply]
    refine (qq D : FI D).coeToSubmodule.neg_mem (Submodule.sum_mem _ fun e _ => ?_)
    rw [Matrix.sub_apply]
    exact mul_mem_qq (hXi1 c e) (hXe e d)
  have hPe : ∀ c d, Psi w X⁻¹ c d - (1 : MatR D) c d ∈ (qq D : FI D) := by
    intro c d
    rw [← Matrix.sub_apply, show Psi w X⁻¹ - 1 = Psi w (X⁻¹ - 1) by rw [Psi_sub, Psi_one]]
    simp only [Formalism.L2.SG.Pf.StabIntLat.Psi]
    exact mul_mem_qq (sign_mem_one c d) (conj_mem_qq (by rw [Matrix.sub_apply]; exact hXie _ _))
  rw [← Xmat_coordX w hU hB, condX_iff, Xmat_coordX w hU hB]
  refine ⟨fun q => mem_dd_of_int (hX1 _ _), fun q => mem_qd_of_qq ?_⟩
  rw [Matrix.sub_apply, show X q.1.1 q.1.2 - Psi w X⁻¹ q.1.1 q.1.2 =
    (X q.1.1 q.1.2 - (1 : MatR D) q.1.1 q.1.2) - (Psi w X⁻¹ q.1.1 q.1.2 - (1 : MatR D) q.1.1 q.1.2) by ring]
  exact (qq D : FI D).coeToSubmodule.sub_mem (hXe _ _) (hPe _ _)

end Formalism.L2.SG.Pf.StabIntCong
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.DeltaAE
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel

namespace Formalism.L2.SG.Pf.StabilizerIndexVolumes

theorem deltaAE_holds (D : D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) : DeltaAE D δ M := by
  intro hA
  have h := Formalism.L2.SG.Pf.LocModel.good_cofinite δ M hA ∅
  rw [Filter.eventually_cofinite] at h
  refine h.subset fun p hp => ?_
  intro hg
  apply hp
  have hδ : δ p ≠ 0 := (hA p).2.1
  have hu : IsUnit (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)) := (isUnit_iff_ne_zero.2 hδ).map _
  have e1 : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)⁻¹ * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hδ, map_one]
  have hinv : Ring.inverse (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)⁻¹ := by
    calc Ring.inverse (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p))
        = Ring.inverse (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)) *
            (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)⁻¹) := by
          rw [mul_comm (algebraMap _ _ (δ p)), e1, mul_one]
      _ = (Ring.inverse (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)) *
            algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)) * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)⁻¹ := by
          rw [mul_assoc]
      _ = _ := by rw [Ring.inverse_mul_cancel _ hu, one_mul]
  rw [hinv, (D.s.atP p).O_def]
  have hmem : (δ p)⁻¹ ∈ 𝒪[(D.s.atP p).Fp] := hg.2.1.2
  have : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)⁻¹ =
      algebraMap 𝒪[(D.s.atP p).Fp] (D.s.atP p).Ep ⟨(δ p)⁻¹, hmem⟩ := rfl
  rw [this]
  exact isIntegral_algebraMap

end Formalism.L2.SG.Pf.StabilizerIndexVolumes
end
end

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2

namespace Formalism.L2.SG.Pf.VolPinAsm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hyps_of {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word) (hPH : PrimeHyp D u (Tu D u')) :
    Formalism.L2.SG.Pf.StabilizerIndexVolumes.Hyps D u u' (X.Fu u) (Y.what₂ u) := by
  refine ⟨PI.TCS.termStable_holds D u u', Formalism.L2.SG.Pf.term_equivalence_iff D u u', term_function_const D u u',
    hPH, D.sp.Y_sig 0, Y.rowsOK u⟩

theorem volIdxFinP (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (hPH : PrimeHyp D u (Tu D u')) :
    Formalism.L2.SG.Pf.StabilizerIndexVolumes.VolumeIndexFiniteNonzero D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M := Formalism.L2.SG.Pf.StabilizerIndexVolumes.volume_index_finite_of_hyps D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M (hyps_of Y u u' hPH)
    Formalism.L2.SG.Pf.StabilizerIndexVolumes.commens Formalism.L2.SG.Pf.StabilizerIndexVolumes.stClosed (Formalism.L2.SG.Pf.StabilizerIndexVolumes.deltaAE_holds D _ _)
    (Formalism.L2.SG.Pf.StabilizerIndexVolumes.volume_index_a_stable D u u' _ _ _ _) (Formalism.L2.SG.Pf.StabIntCong.aBddOf u u' _ _ _ _)
    (Formalism.L2.SG.Pf.StabIntCong.aCong u u' _ _ _ _) (Formalism.L2.SG.Pf.StabilizerIndexVolumes.volume_index_b_stable D u u' _ _ _ _)
    (Formalism.L2.SG.Pf.StabilizerIndexVolumes.volume_index_b_bounded D u u' _ _ _ _) (Formalism.L2.SG.Pf.StabilizerIndexVolumes.volume_index_b_congruence D u u' _ _ _ _)

theorem volume_generic_odd_of_rep (hD : DictC) (hC : CovolOne3C) : Formalism.L2.SG.VolPin.VolumeOddGeneric := by
  refine volume_generic_odd_of hD hC (fun D X Y u u' hPH t w F' L U hrel hgen hNR hG => ?_)
    (fun D X Y u u' h => volIdxFinP D X Y u u' h)
  exact Formalism.L2.SG.Pf.StabilizerIndexVolumes.volume_index_b_stable D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M Formalism.L2.SG.Pf.StabilizerIndexVolumes.stClosed
    (hyps_of Y u u' hPH) Y.agree t.toTerm w F' L U hrel hgen hNR hG

end Formalism.L2.SG.Pf.VolPinAsm
end
end

namespace Formalism.L2.SG.Closed

theorem volume_determined : Formalism.L2.SG.VolPin.VolumeOddGeneric :=
  Formalism.L2.SG.Pf.VolPinAsm.volume_generic_odd_of_rep Formalism.L2.SG.Pf.VolPinAsm.dictC_holds Formalism.L2.SG.NGCut.StabilizerCovolume.covolOne3C_holds

end Formalism.L2.SG.Closed
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.NuQPinExistsHolds
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
open Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.SpectralTiesReal

namespace Formalism.L2.SG.PoincareAmplitudeLowerBounds

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.DataInst Formalism.L2.SG.CntLocal Formalism.L2.SG.RowsConc Formalism.L2.SG.RealObj

theorem massDataY_tt {D : D7} (T : STies D) (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin T.X.B.I.n → T.X.B.I.E)
    (sd C Th : ℝ) (vR : Formalism.L2.SG.TermDef.Term D u u' (T.X.Fu u) (T.Y.what₂ u) → ℝ)
    (Q : Formalism.L2.SG.PairVal.PairSys D u u' (T.X.Fu u) (T.Y.what₂ u))
    (i0 i0' : ∀ _ : InfinitePlace T.X.B.I.F, Fin D.R.k) (νq : T.X.B.I.Ginf → Measure T.X.B.I.Ginf) :
    (massDataY T.X T.hb T.Y u u' X0 T.ψ sd C Th vR Q i0 i0' νq).tt = PgC T.Y := by
  have h1 := Formalism.L2.SG.MassDataConc.ttC_of_split T.X T.hb T.Y.hK (T.Y.FN u) (T.Y.FN u') u u' X0 T.ψ (T.Y.tO u u') sd C Th vR Q
    T.Y.M T.Y.δ i0 i0' νq (Formalism.L2.SG.Pf.gSplitX_holds T.X)
  unfold Formalism.L2.SG.MassDataConc.ttC at h1
  rw [h1, PgC, Formalism.L2.SG.Pf.tt_eq_holds T.X T.Y.TR]
  have hS := Formalism.L2.SG.Pf.gSplitX_holds T.X
  have e : ∀ p : Formalism.L2.SG.TypedSets.TypX T.X,
      (1 + 3 / ((Ideal.absNorm p.1.asIdeal : ℕ) : ℝ)) = (fun q : ℕ => 1 + 3 / (q : ℝ)) (Formalism.L2.SG.TypedSets.gOf p) := by
    intro p
    rw [(hS p).1]
    rfl
  rw [Finset.prod_congr rfl fun p _ => e p]
  have hq : ∀ p : Formalism.L2.SG.TypedSets.TypX T.X,
      Formalism.L2.SG.TypedSets.gOf p = D.host.g 0 ∨ Formalism.L2.SG.TypedSets.gOf p = D.host.g 1 := by
    intro p; unfold Formalism.L2.SG.TypedSets.gOf; split_ifs <;> simp
  have h2 := Formalism.L2.SG.Pf.SatGram.prod_two (M := ℝ) (fun p : Formalism.L2.SG.TypedSets.TypX T.X => Formalism.L2.SG.TypedSets.gOf p)
    (D.host.g 0) (D.host.g 1) D.host.g_ne hq (fun q : ℕ => 1 + 3 / (q : ℝ))
  refine h2.trans ?_
  rw [Formalism.L2.SG.Pf.SatGram.card_typ (Formalism.L2.SG.Pf.SatGram.gCount_of Formalism.L2.SG.Pf.SatGramLoc.split_prime_local_holds) 0,
    Formalism.L2.SG.Pf.SatGram.card_typ (Formalism.L2.SG.Pf.SatGram.gCount_of Formalism.L2.SG.Pf.SatGramLoc.split_prime_local_holds) 1]

theorem idZero_tO {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word) (hne : u ≠ u')
    (hWD : Formalism.L2.SG.WuDecay.WuDecay X) : (Y.tO u u').IdZero := by
  have hF := Formalism.L2.SG.Pf.fundExistsC_holds D X Y u u'
  have hO := Formalism.L2.SG.Pf.KernelOfEmbedding.ooIntAll_of (Y := Y) hWD u u'
  have hI := Formalism.L2.SG.Pf.idCellOffC_holds_of_vol Formalism.L2.SG.Closed.VolPosC_holds D X Y u u' hF hO hne
  have hc : Continuous (Formalism.L2.SG.PackageTie.hsEmb (Wq := Formalism.L2.SG.TermOp.CM (Y.cs u'))
      (Wp := Formalism.L2.SG.TermOp.CM (Y.cs u))) := LinearMap.continuous_of_finiteDimensional _
  have h2 := hI.map (Formalism.L2.SG.PackageTie.hsEmb (Wq := Formalism.L2.SG.TermOp.CM (Y.cs u'))
      (Wp := Formalism.L2.SG.TermOp.CM (Y.cs u))).toAddMonoidHom hc
  simp only [LinearMap.toAddMonoidHom_coe, map_zero] at h2
  unfold Formalism.FourierDecayAlt.PB.Terms.IdZero Formalism.FourierDecayAlt.PB.Terms.part
  rw [← tsum_subtype]
  exact h2.tsum_eq

theorem splitAll_holds : SplitAll := by
  intro D T u u' X0 C Th Q i0 i0' νq Lsp ϖ hne hSt hCT hg3
  have hWD : Formalism.L2.SG.WuDecay.WuDecay T.X := hCT.2.2.2.2.1
  have hAbs : (T.Y.tO u u').AbsConv :=
    Formalism.L2.SG.Pf.absConvC_outright D T.X T.Y u u'
      (Formalism.L2.SG.Closed.FoldOKC_outright D T.X T.Y u (Formalism.L2.SG.Closed.level_subgroup_properties T.X) hWD)
      (Formalism.L2.SG.Closed.FoldOKC_outright D T.X T.Y u' (Formalism.L2.SG.Closed.level_subgroup_properties T.X) hWD)
      (Formalism.L2.SG.Pf.fundExistsC_holds D T.X T.Y u u')
      (Formalism.L2.SG.Pf.KernelOfEmbedding.ooIntAll_of (Y := T.Y) hWD u u')
  have hq : ∀ v, 3 ≤ Fintype.card (T.Y.TR.Fq v) := fun v => by
    rcases T.Y.TR.card_q v with h | h <;> rw [h] <;> exact hg3 _
  rw [massDataY_tt]
  exact ⟨hAbs, Formalism.L2.SG.RowsConc.normExpSatTied_holds D T.X T.Y u u' hCT,
    Formalism.L2.SG.TermOp.ggBound T.Y.TR (T.Y.cs u) (T.Y.cs u') (T.Y.FN u) (T.Y.FN u')
      Formalism.L2.SG.Closed.TermsGGBound_holds T.Y.psi_ne hq,
    Formalism.L2.SG.TermOp.rowOrth T.Y.TR (T.Y.cs u) (T.Y.cs u') (T.Y.FN u) (T.Y.FN u'),
    Formalism.L2.SG.Pf.SatGram.corankPos_tO T.Y u u', idZero_tO T.Y u u' hne hWD,
    Formalism.L2.SG.TermOp.GG_diag T.Y.TR (T.Y.cs u) (T.Y.cs u') (T.Y.FN u) (T.Y.FN u')⟩

section Link

def KppVolAll : Prop :=
  ∀ (D : D7) (T : STies D) (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin T.X.B.I.n → T.X.B.I.E),
    u ≠ u' → Formalism.MainNotions.S.Cnt.Stand D u u' → ConcTie T.X T.Y →
    (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.gramE T.X.B.I.cm.sig T.X.B.I.J X0).det ≠ 0 →
    Formalism.L2.SG.TypedSets.KppVolAt T.X T.hb T.Y.hK (T.Y.FN u) (T.Y.FN u') u u' X0
      (Formalism.L2.SG.LocVol.locOf T.X u u' T.ψ) (Formalism.L2.SG.NGAnalytic.MassDataLemmas.canonicalAnalyticData T.X T.Y u u' T.ψ)

theorem exists_typ {D : D7} (X : HidaSetting D) :
    ∃ typ : Formalism.L2.SG.TypedSets.TypX X ≃ Bool × InfinitePlace D.host.E, ∀ p,
      (Formalism.L2.SG.TypedSets.gOf p : ℝ) = if (typ p).1 then (D.host.g 0 : ℝ) else (D.host.g 1 : ℝ) := by
  classical
  set q : Formalism.L2.SG.TypedSets.TypX X → Prop := fun p => Formalism.L2.SG.TypedSets.gOf p = D.host.g 0 with hq
  have hcE : Fintype.card (InfinitePlace D.host.E) = D.R.f := Formalism.MainNotions.InterlacingSignCuts.card_places D
  have hc : ∀ i : Fin 2, Fintype.card {p : Formalism.L2.SG.TypedSets.TypX X // Formalism.L2.SG.TypedSets.gOf p = D.host.g i} = D.R.f := by
    intro i
    rw [← Nat.card_eq_fintype_card, Nat.card_congr (Formalism.L2.SG.Pf.DstarIdxPf.typEquiv X i),
      Formalism.L2.SG.Pf.DstarIdxPf.card_over X i]
  have hneg : ∀ p : Formalism.L2.SG.TypedSets.TypX X, ¬ q p ↔ Formalism.L2.SG.TypedSets.gOf p = D.host.g 1 := by
    intro p
    simp only [hq]
    constructor
    · intro h; unfold Formalism.L2.SG.TypedSets.gOf at h ⊢; split_ifs at h ⊢ <;> simp_all
    · intro h e; exact D.host.g_ne (e.symm.trans h)
  have e0 : {p // q p} ≃ InfinitePlace D.host.E := Fintype.equivOfCardEq (by rw [hc 0, hcE])
  have e1 : {p // ¬ q p} ≃ InfinitePlace D.host.E :=
    Fintype.equivOfCardEq (by rw [Fintype.card_congr (Equiv.subtypeEquivRight hneg), hc 1, hcE])
  let typ : Formalism.L2.SG.TypedSets.TypX X ≃ Bool × InfinitePlace D.host.E :=
    (Equiv.sumCompl q).symm.trans ((Equiv.sumComm _ _).trans ((Equiv.sumCongr e1 e0).trans
      (Equiv.boolProdEquivSum (InfinitePlace D.host.E)).symm))
  refine ⟨typ, fun p => ?_⟩
  by_cases h : q p
  · have : (typ p).1 = true := by
      simp [typ, Equiv.sumCompl_symm_apply_of_pos h, Equiv.boolProdEquivSum]
    rw [this, if_pos rfl]
    exact_mod_cast h
  · have : (typ p).1 = false := by
      simp [typ, Equiv.sumCompl_symm_apply_of_neg h, Equiv.boolProdEquivSum]
    rw [this, if_neg (by simp)]
    exact_mod_cast (hneg p).1 h

theorem linkAll_of (hKpp : KppVolAll) : LinkAll := by
  intro D T u u' e τ X0 C Th Q i0 i0' νq Lsp ϖ hne hSt hCT hdet hDst
  have hH : Formalism.L2.SG.TypedSets.HypX T.X T.hb (T.Y.FN u) (T.Y.FN u') u u' :=
    ⟨T.measTie, Formalism.L2.SG.Closed.level_subgroup_properties T.X, T.Y.FN_fund u, T.Y.FN_fund u'⟩
  have hG := Formalism.L2.SG.IntegralApproximation.Gam1TieC_holds T.X T.hb T.Y.hK (T.Y.FN u) (T.Y.FN u') u u' X0 T.ψ
    (supDens Lsp T.Y.δ ϖ u u' (T.X.Fu u) (T.Y.what₂ u) / ∏' p, alpD u u' p) C Th
    (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) Q T.Y.M T.Y.δ i0 i0' νq T.Y
  have hD := Formalism.L2.SG.IntegralApproximation.MassDataDstarX_holds T.X T.hb T.Y.hK (T.Y.FN u) (T.Y.FN u') u u' X0 T.ψ (T.Y.tO u u')
    (supDens Lsp T.Y.δ ϖ u u' (T.X.Fu u) (T.Y.what₂ u) / ∏' p, alpD u u' p) C Th
    (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) Q T.Y.M T.Y.δ i0 i0' νq
    (Formalism.L2.SG.LocVol.locOf T.X u u' T.ψ) (Formalism.L2.SG.NGAnalytic.MassDataLemmas.canonicalAnalyticData T.X T.Y u u' T.ψ) hH
    (hKpp D T u u' X0 hne hSt hCT hdet)
  obtain ⟨typ, htyp⟩ := exists_typ T.X
  refine ⟨hG, Formalism.L2.SG.MassDataConc.pairSum_eq _ hG, ⟨typ, htyp⟩, hCT.2.2.1 u, hCT.2.2.1 u', ?_⟩
  rw [hDst]
  exact hD.trans hCT.2.2.2.1

end Link

section Choices

open ValuativeRel

def NuQPinExists : Prop :=
  ∀ (D : D7) (T : STies D) (u u' : D.what₂.Word), u ≠ u' → Formalism.MainNotions.S.Cnt.Stand D u u' →
    ∃ νq : T.X.B.I.Ginf → Measure T.X.B.I.Ginf, NuQPin T.X u u' νq

def LocSpExists : Prop := ∀ (D : D7) (T : STies D), Nonempty (LocSp D T.Y.M)

theorem choicesC_of (hNu : NuQPinExists) (hL : LocSpExists) : ChoicesC := by
  intro D T u u' hne hSt _ hk
  obtain ⟨νq, hνq⟩ := hNu D T u u' hne hSt
  obtain ⟨X0, hX0⟩ := Formalism.L2.SG.NGLeaves.nondegenerate_gram_tuple D T.X
  obtain ⟨Lsp⟩ := hL D T
  have hϖ : ∀ p : PlF D, ∃ x : 𝒪[(D.s.atP p).Fp], Irreducible x := fun p => by
    haveI := (D.s.atP p).lf
    exact IsDiscreteValuationRing.exists_irreducible _
  choose ϖ hϖ' using hϖ
  obtain ⟨κ, hκ⟩ := Formalism.L2.SG.DataCut.rowLabelExists_holds D u u' (T.X.Fu u) (T.Y.what₂ u) (T.Y.rowsOK u)
  let i0 : ∀ _ : InfinitePlace T.X.B.I.F, Fin D.R.k := fun _ => ⟨0, by omega⟩
  exact ⟨i0, i0, νq, X0, Lsp, ϖ, κ, Formalism.L2.SG.NGAnalytic.MassDataLemmas.pairSys0 u u' (T.X.Fu u) (T.Y.what₂ u),
    fun _ => rfl, Formalism.L2.SG.RealObj.InfCut.real_point_representative_exists D T.X u u' 1 one_pos i0, hνq, hX0, hϖ', hκ⟩

end Choices

section Leaves

theorem kppVolAll_holds : KppVolAll :=
  fun _ T u u' X0 _ _ _ _ => kpp_volume_at_instance T.X T.hb T.Y.hK _ _ u u' X0 _ _

theorem linkAll_holds : LinkAll := linkAll_of kppVolAll_holds

theorem nuQPinExists_holds : NuQPinExists := by
  intro D T u u' _ _
  have hP : Formalism.L2.SG.NGPin.PinHaarEx := Formalism.L2.SG.NGPin.pinHaarEx_of_place
    (Formalism.L2.SG.RootPatterns.placeHaar_of_loc Formalism.L2.SG.NGPin.locRootHaar_holds)
  exact ⟨fun γ => (Formalism.L2.SG.NGPin.exists_at T.X u u' hP γ).choose,
    fun γ h => (Formalism.L2.SG.NGPin.exists_at T.X u u' hP γ).choose_spec.1 h,
    fun w hw => (Formalism.L2.SG.NGPin.exists_at T.X u u' hP (gamW T.X u u' w)).choose_spec.2.2 w hw rfl⟩

theorem locSpExists_holds : LocSpExists := fun D T =>
  ⟨{ V := Formalism.L2.SG.TermLoc.Vp D
     H := fun p => Formalism.L2.SG.TermLoc.locHerm T.Y.M p (T.Y.agree p).2.2.1
     rank := Formalism.L2.SG.TermLoc.finrank_Vp
     bc := Formalism.L2.SG.TermLoc.baseChange₂ D
     bc_smul := Formalism.L2.SG.TermLoc.baseChange_smul₂
     bc_span := Formalism.L2.SG.TermLoc.span_baseChange_eq_top
     bc_form := fun p x y => Formalism.L2.SG.TermLoc.baseChangeAt_form T.Y.M p (T.Y.agree p).2.2.1 x y }⟩

theorem choicesC_holds : ChoicesC := choicesC_of nuQPinExists_holds locSpExists_holds

end Leaves

end Formalism.L2.SG.PoincareAmplitudeLowerBounds
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXVolAll
namespace Formalism.L2.SG.Pf.MassDataX

theorem massDataVolAll_of (hSW : PI.VolStabS.MassDataS.SWXS) :
    Formalism.L2.SG.PoincareAmplitudeLowerBounds.MassDataVolAll := by
  intro D T u u' X0 sd C Th Q i0 i0' νq
  refine ⟨PI.VolStabS.MassDataS.inVolumesAt_of_SWS hSW _ _ _ _ _ _ _ _ _ _, ?_, ?_, ?_, ?_⟩
  · first
      | apply level_s_at_instance
      | apply PI.Final.level_s_at_instance
      | apply PI.level_s_at_instance
      | apply MassDataLevelSSteps.inLevelSAt_holds
      | apply PI.MassDataLevelSSteps.inLevelSAt_holds
      | apply PI.UnitaryGroupMassFormula.MassDataLevelSSteps.inLevelSAt_holds
  · apply inMassesAt_holds
  · apply inColumnsAt_holds
  · apply inIndicesAt_holds

end Formalism.L2.SG.Pf.MassDataX
end

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
open Formalism.L2.SG.SpectralTiesReal Formalism.L2.SG.PoincareAmplitudeLowerBounds

namespace Formalism.L2.SG.TheoremSConclusion

def TheoremSClosedHypotheses : Prop :=
  (∀ D : D7, Formalism.L2.SG.DataInst.LocalModelAt D) ∧ (∀ D : D7, Formalism.L2.SG.Pf.LocCP.LocTied D → Formalism.L2.SG.DataInst.DensInputAt D) ∧
  (∀ D : D7, Formalism.L2.SG.SpectralTiesReal.RowsInputP D) ∧ Formalism.L2.SG.RowsPos.RowNGP ∧ Formalism.L2.SG.RowsConc.KppOffC ∧ CarrierP ∧
  KernelExponentAgreement ∧ Formalism.L2.SG.Full.FoldOKC ∧ Formalism.L2.SG.Full.OOIntAllC ∧ Formalism.L2.SG.Full.AbsConvC ∧ FinXC ∧
  Formalism.L2.SG.Pf.WuDecayOfGap ∧ ChoicesC ∧ FormulaC ∧ RowsSumC ∧ RowFormAllP ∧ MassDataHypAll ∧ LinkAll ∧ SplitAll

theorem rowsInputP_of_dataCut {D : D7} (h : Formalism.L2.SG.DataCut.RowsInputP D) : Formalism.L2.SG.SpectralTiesReal.RowsInputP D :=
  fun Wp Wq _ _ _ _ S δ M hA L u u' hT hC hPH F0 what₂ hR ϖ hϖ nc hF α hα hB =>
    h Wp Wq S δ M hA L u u' hT hPH hC F0 what₂ hR ϖ hϖ nc hF α hα hB

theorem theoremS_of_conj (h : TheoremSClosedHypotheses) (Cthr : ℝ) :
    ∃ C₄ CA C : ℝ, 1 ≤ C₄ ∧ Cthr ≤ CA ∧ 1 ≤ CA ∧ 0 ≤ C ∧ C ≤ CA ∧
    ∀ (C0 CG CDel cT Cb : ℝ), 1 ≤ C0 → 0 ≤ CG → 4 < CDel → 0 < cT → 0 < Cb → 1 < cT * Cb →
    ∃ k0 : ℕ, ∀ Cg cb Cw cTf CT C0f : ℝ, 0 < cb → 0 < cTf → ∃ Cn C'₀ Cl₀ : ℝ, 0 ≤ Cn ∧ ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (L : SizeData₂ D) (T : STies D) (u u' : D.what₂.Word), Formalism.BasicNotions.Ties D → u ≠ u' → 0 ≤ L.sc.b →
      SizesAt CA C0 CG CDel cT Cb Cn k0 D L T u u' →
      Formalism.MainNotions.S.Cnt.Hyp0 D L C' Cl Cg cb Cw cTf CT C0f → Formalism.MainNotions.S.Cnt.Stand D u u' →
      Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D L C' Cl Cg cb Cw cTf CT C0f →
      Formalism.L2.SG.ConcreteSettingExists.GapHyp D → Formalism.L2.SG.Pf.LocCP.LocTied D → Formalism.L2.SG.RowsConc.TFrameAt D →
      (T.Y.tO u u').RowBig (Formalism.L2.SG.RowsConc.epsL D) (Formalism.L2.SG.RowsConc.ddC T.X T.Y u u') →
      (T.Y.tO u u').RowNotScalar (Formalism.L2.SG.RowsConc.epsL D) (Formalism.L2.SG.RowsConc.ddC T.X T.Y u u') →
      ‖(T.Y.tO u u').K0‖ ^ 2 ≤ (1 + (L.sc.b ^ 6)⁻¹) * ((D.duS u : ℝ) * (D.duS u') / D.what₂.Dstar) ∧
      L.hsSq u u' ≤ (1 + L.sc.b ^ (-(6 : ℝ))) * (D.duS u : ℝ) * (D.duS u' : ℝ) / D.what₂.Dstar := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩ := h
  exact theoremS_closedP h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 Cthr

theorem kExpTiedS_holds : KernelExponentAgreement := by
  intro D X Y u u' hT
  have f1 := Formalism.L2.SG.Closed.FoldOKC_outright D X Y u hT.1 hT.2.2.2.2.1
  have f2 := Formalism.L2.SG.Closed.FoldOKC_outright D X Y u' hT.1 hT.2.2.2.2.1
  have hFE := Formalism.L2.SG.Pf.fundExistsC_holds D X Y u u'
  have hOO := Formalism.L2.SG.Closed.OOIntAllC_outright D X Y u u' f1 f2 hFE
  exact Formalism.L2.SG.Closed.KExpansionC_holds D X Y u u' f1 f2
    (Formalism.L2.SG.Closed.InHHC_holds D X Y u hT.2.2.2.2.2.1 f1) (Formalism.L2.SG.Closed.InHHC_holds D X Y u' hT.2.2.2.2.2.1 f2) hFE hOO
    (Formalism.L2.SG.Closed.OOFundIndepC_holds D X Y u u' hFE hOO) (Formalism.L2.SG.Closed.AmpWellDefC_holds D X Y u u' hOO)
    (Formalism.L2.SG.Closed.AbsConvC_outright D X Y u u' f1 f2 hFE hOO)

end Formalism.L2.SG.TheoremSConclusion
