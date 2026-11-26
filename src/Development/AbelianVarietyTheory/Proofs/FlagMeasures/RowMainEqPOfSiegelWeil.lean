module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsPos
public import CompanionTheory.AutomorphicTheory.UniformLocalFormulas.Closed
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyGroupSumFactorsRowWeightAmplitudeProof
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WuDecayOfGap
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyLocalObjectsExistAtTermsProof
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyGenericMassPositiveBoundedProof

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowMainEqPOfSiegelWeilConstants
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericFamilyStepOfSiegelWeil
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericRowFamilyStepOfLeaves
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericRowFamilyStepOfLeaves
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc
  Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqFam Formalism.MainNotions.S.LocNG GlobalTheory.SnFam

namespace GlobalTheory.SnFam.Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem ampQ_not_eq_ampG' {Cl Nu : Type} (L : PN.LocalNG Cl Nu) : ampQ Not L = ampG L := by
  funext d
  unfold ampQ ampG
  rw [Finset.sum_eq_single_of_mem ∅ (by simp)]
  · simp
  · intro A hA hne
    simp only [Finset.mem_filter, Finset.not_nonempty_iff_eq_empty] at hA
    exact absurd hA.2 hne

private theorem hasPt_of_isPtG {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word)
    (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ) (γ : PN.Pts D.host.E D.R.rS)
    (h : PN.IsPt (genT (Y.tO u u)) (NOfG Y u νL νB ng) γ) : HasPt Y u u (Y.tO u u).genSet γ := by
  obtain ⟨c, ν, t, ht, hv, -, hpt, -⟩ := h
  refine ⟨t, ?_, ?_, ?_⟩
  · simpa [genT, PB.Terms.ngSet, PB.Terms.genSet] using ht
  · simpa [genT] using hv
  · simpa [NOfG] using hpt

theorem stepFamG_of_fam : (∀ D : D7, 4 * D.R.rS + 7 ≤ D.R.k → Formalism.L2.SG.FamDefs.LocalLowerBoundAllCosets D.R.k D.R.rS 9) →
    Formalism.L2.SG.FamDefs.HTie → FamGen → FamilyWeightSumUnfoldingIdentity → WeightsFam → FamilyGroupSumFactorsWeightAmplitude → ExistFam →
    Formalism.L2.SG.Pf.MainEqFam.StepFamG := by
  intro hG6 hH hGen hG5 hW hG4 hE Cg cb Cw cT CT C0
  obtain ⟨aH, bH, hH'⟩ := hH Cg cb Cw cT CT C0
  obtain ⟨aF, bF, hF'⟩ := hGen Cg cb Cw cT CT C0
  obtain ⟨a5, b5, h5⟩ := hG5 Cg cb Cw cT CT C0
  obtain ⟨aW, bW, hW'⟩ := hW Cg cb Cw cT CT C0
  obtain ⟨CSt, hCSt, a4, b4, h4⟩ := hG4 Cg cb Cw cT CT C0
  obtain ⟨aE, bE, hE'⟩ := hE Cg cb Cw cT CT C0
  refine ⟨9, CSt, hCSt, max aH (max aF (max a5 (max aW (max a4 aE)))),
    max bH (max bF (max b5 (max bW (max b4 bE)))), ?_⟩
  intro C' Cl hC' hCl D large₂ X Y u hc hb X0 ψ hbt sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hbk ν hpin
  simp only [max_le_iff] at hC' hCl
  obtain ⟨s, hs1, hs2, hs3, hs4⟩ := h4 C' Cl hC'.2.2.2.2.1 hCl.2.2.2.2.1 D large₂ X Y u u hc hb X0 ψ hbt sd C Th F0
    what₂ vR Q i0 i0' νq Irat Ire hbk ν hpin
  refine ⟨s, hs1, hs2, hs3, ?_⟩
  intro γ hγ S
  have hQ := hF' C' Cl hC'.2.1 hCl.2.1 D large₂ X Y u u hc
  have hP := hasPt_of_isPtG Y u (sc s ν) ν (fun _ => 0) γ hγ
  obtain ⟨Fm, hT, hRel, hTerm, hDs, hrw⟩ :=
    hE' C' Cl hC'.2.2.2.2.2 hCl.2.2.2.2.2 D large₂ X Y u u hc _ Not _ _ hQ γ hP
  have h5' : OrbitFamilyIdentityAt Fm Fm.V0 := Formalism.L2.SG.FamDefs.orbitFamilyIdentity_at_volume hT (h5 C' Cl hC'.2.2.1 hCl.2.2.1 D large₂ X Y u u hc _ Not _ _ hQ γ hP Fm hT)
  obtain ⟨hWpos, hWle⟩ := hW' C' Cl hC'.2.2.2.1 hCl.2.2.2.1 D large₂ X Y u u hc hb X0 ψ hbt sd C Th F0 what₂ vR Q i0 i0' νq
    Irat Ire hbk _ Not _ _ hQ γ hP Fm hT hRel hTerm h5'
  have hHt := hH' C' Cl hC'.1 hCl.1 D large₂ X Y u u hc _ _ _ γ Fm hT
  refine ⟨Fm, Formalism.L2.SG.FamDefs.famOKS_of (NOfG Y u (sc s ν) ν (fun _ => 0)) γ S
    (PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq).AA) (fun L => ampG L) Fm hT hRel hTerm
    hDs hrw (hG6 D (Formalism.L2.SG.FamDefs.four_rank_add_seven_le_k hc)) h5' ?_ hWpos ?_ ?_⟩
  · simpa [NOfG] using hHt
  · simpa [NOfG] using hWle
  · intro x _
    have h := hs4 _ Not _ _ hQ γ hP Fm hT x.1 x.2
    rw [ampQ_not_eq_ampG'] at h
    rw [← h]
    rfl

end GlobalTheory.SnFam.Gen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericRowFamilyStepOfLeavesStatement
open GlobalTheory.SnFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericRow_familyStep_of_leaves : (∀ D : Formalism.BasicNotions.D7, 4 * D.R.rS + 7 ≤ D.R.k → Formalism.L2.SG.FamDefs.LocalLowerBoundAllCosets D.R.k D.R.rS 9) → Formalism.L2.SG.FamDefs.HTie → FamGen → FamilyWeightSumUnfoldingIdentity → WeightsFam → FamilyGroupSumFactorsWeightAmplitude → ExistFam → Formalism.L2.SG.Pf.MainEqFam.StepFamG := by
  first | exact @GlobalTheory.SnFam.Gen.stepFamG_of_fam | exact GlobalTheory.SnFam.Gen.stepFamG_of_fam | (intros; apply GlobalTheory.SnFam.Gen.stepFamG_of_fam <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericScalarClassTermsFormFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ScalarCorankOnePairsTrans
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ScalarCorankOnePairsTrans
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ScalTrans

open Module

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

theorem isScalar_trans {Λ : Submodule (𝓞 E) S.V} {r k : ℕ} {T T' : E} {F : LFlag S r T}
    {F' F'' F''' : LFlag S r T'} {β γ : S.V ≃ₗ[E] S.V}
    (hΛ : Submodule.IsFullLattice E Λ) (hdim : finrank E S.V = k + 2 * r + 1)
    (hF : IsLift Λ F) (hL' : IsLift Λ F') (hG' : Gval F F' ≠ 0) (hL'' : IsLift Λ F'')
    (hG'' : Gval F F'' ≠ 0) (hi : β ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (hX : ∀ j, (Xflag F' j).map (β : S.V →ₗ[E] S.V) = Xflag F'' j) (hz : β F'.fl.z = F''.fl.z)
    (hs1 : s0 Λ F F' F'' β k = 1) (hS1 : IsScalar Λ F F' F'' β) (hS2 : IsScalar Λ F F'' F''' γ) :
    IsScalar Λ F F' F''' (β.trans γ) := by
  have n' := _root_.PI.UnitaryGroupMassFormula.ScalEquivGen.ndOfQ hΛ hF hL' hG'
  have n'' := _root_.PI.UnitaryGroupMassFormula.ScalEquivGen.ndOfQ hΛ hF hL'' hG''
  have hTh1'' := _root_.PI.UnitaryGroupMassFormula.ScalEquivGen.thEq''Q hΛ hdim n' n'' hs1
  intro y1 hy1 y3 hy3 y1' hy1' y3' hy3' h13 h31 al al'
  have hy1b : y1 ∈ orth S (Xplus F) := hy1.2
  have hy1'b : y1' ∈ orth S (Xplus F') := hy1'.2
  have hy2 : y1 ∈ Ylift Λ F F'' :=
    Submodule.mem_inf.mpr ⟨_root_.PI.UnitaryGroupMassFormula.ScalEquivGen.yliftMemQ hTh1'' hy1, hy1b⟩
  have hy2' : β y1' ∈ Ylift' Λ F F'' :=
    Submodule.mem_inf.mpr ⟨_root_.PI.UnitaryGroupMassFormula.ScalEquivGen.ylift'MemQ hi hX hTh1'' hy1',
      _root_.PI.UnitaryGroupMassFormula.ScalEquivGen.mapOrthXplusQ hi hX hz hy1'b⟩
  have a := hS1 y1 hy1 y1 hy2 y1' hy1' (β y1') hy2' (by simp) (by simp) al al'
  have b := hS2 y1 hy2 y3 hy3 (β y1') hy2' y3' hy3' h13 h31 al al'
  exact a.trans b

end Gen

theorem scalar_pair_trans : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    ∀ t t' t'' : TauC Y u u', t.G ≠ 0 → t'.G ≠ 0 → t''.G ≠ 0 →
    (Y.tO u u').s0 t t' = 1 → (Y.tO u u').scal t t' → (Y.tO u u').s0 t' t'' = 1 →
    (Y.tO u u').scal t' t'' → (Y.tO u u').s0 t t'' = 1 ∧ (Y.tO u u').scal t t'' := by
  intro D X Y u u' t t' t'' hG hG' hG'' h1 hsc1 h2 hsc2
  have hdim := Formalism.L2.SG.Corank.finrank_VS D
  have hGv : ∀ s : TauC Y u u', s.G ≠ 0 → Gval (lf D (X.Fu u)) s.frame ≠ 0 := fun s hs h =>
    hs ((Formalism.L2.SG.Pf.SatGram.gterm_G Y s).trans h)
  have hfull : Submodule.IsFullLattice D.host.E t.lam := ((Y.rowsOK u).1 t.lam t.mem).1.1
  have hLF : IsLift t.lam (lf D (X.Fu u)) := ((Y.rowsOK u).1 t.lam t.mem).2.1.2.2.1
  have hLt : ∀ s : TauC Y u u', IsLift s.lam s.frame := fun s => s.rep.2.2.2.2.1
  obtain ⟨⟨hl1, hl1'⟩, hs1, hS1⟩ := (show scalT t t' from hsc1)
  obtain ⟨⟨hl2, hl2'⟩, hs2, hS2⟩ := (show scalT t' t'' from hsc2)
  rw [← hl1] at hs2 hS2
  have hL' : IsLift t.lam t'.frame := by rw [hl1]; exact hLt t'
  have hL'' : IsLift t.lam t''.frame := by rw [hl1, hl2]; exact hLt t''
  have hth1 := (Formalism.L2.SG.NGCut.CorankRelation.s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam hfull _ t.frame t'.frame _ hLF (hLt t)
    (hGv t hG)).1 hs1
  have hth2 := (Formalism.L2.SG.NGCut.CorankRelation.s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam hfull _ t'.frame t''.frame _ hLF hL'
    (hGv t' hG')).1 hs2
  have htr := Formalism.L2.SG.NGCut.CorankRelation.Th_trans t.lam _ t.frame t'.frame t''.frame (t'.lin * t.lin⁻¹)
    (t''.lin * t'.lin⁻¹) (fun x hx => (Formalism.L2.SG.NGCut.CorankRelation.frame_mem_iff t' t'' x).1 hx) hth1 hth2
  have hmul : (t''.lin * t'.lin⁻¹) * (t'.lin * t.lin⁻¹) = t''.lin * t.lin⁻¹ := by group
  rw [hmul] at htr
  have hs3 : Lat.s0 t.lam (lf D (X.Fu u)) t.frame t''.frame (t''.lin * t.lin⁻¹) D.R.k = 1 :=
    (Formalism.L2.SG.NGCut.CorankRelation.s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam hfull _ t.frame t''.frame _ hLF (hLt t) (hGv t hG)).2 htr

  have hi1 := t.rep.2.2.1
  have hi2 := t'.rep.2.2.1
  have hiβ : t'.lin * t.lin⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT :=
    (Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem hi2 ((Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem hi1)
  have hX : ∀ j, (Xflag t.frame j).map ((t'.lin * t.lin⁻¹ : (VS D).V ≃ₗ[D.host.E] (VS D).V) :
      (VS D).V →ₗ[D.host.E] (VS D).V) = Xflag t'.frame j := by
    intro j
    unfold GTerm.frame
    rw [Formalism.L2.SG.Pf.MainEqClass.xflag_mapLF' t.lin hi1, Formalism.L2.SG.Pf.MainEqClass.xflag_mapLF' t'.lin hi2,
      ← Submodule.map_comp]
    congr 1
    ext x
    simp
  have hz : (t'.lin * t.lin⁻¹) t.frame.fl.z = t'.frame.fl.z := by
    unfold GTerm.frame
    rw [Formalism.L2.SG.Pf.MainEqClass.z_mapLF' t.lin hi1, Formalism.L2.SG.Pf.MainEqClass.z_mapLF' t'.lin hi2]
    simp
  have hsc3 := isScalar_trans (β := t'.lin * t.lin⁻¹) (γ := t''.lin * t'.lin⁻¹) hfull hdim hLF (hLt t) (hGv t hG) hL'
    (hGv t' hG') hiβ hX hz hs1 hS1 hS2
  have e3 : (t'.lin * t.lin⁻¹).trans (t''.lin * t'.lin⁻¹) = t''.lin * t.lin⁻¹ := hmul
  rw [e3] at hsc3
  have hl : t.lam = t''.lam ∧ t.lam' = t''.lam' := ⟨hl1.trans hl2, hl1'.trans hl2'⟩
  refine ⟨?_, ?_⟩
  · show s0T t t'' = 1
    unfold s0T
    rw [if_pos hl]
    exact hs3
  · show scalT t t''
    exact ⟨hl, hs3, hsc3⟩

end GlobalTheory.ScalTrans
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ScalarCorankOnePairsTransStatement
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalarCorankOnePairs_trans : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ t t' t'' : TauC Y u u', t.G ≠ 0 → t'.G ≠ 0 → t''.G ≠ 0 → (Y.tO u u').s0 t t' = 1 → (Y.tO u u').scal t t' → (Y.tO u u').s0 t' t'' = 1 → (Y.tO u u').scal t' t'' → (Y.tO u u').s0 t t'' = 1 ∧ (Y.tO u u').scal t t'' := by
  first | exact @GlobalTheory.ScalTrans.scalar_pair_trans | exact GlobalTheory.ScalTrans.scalar_pair_trans | (intros; apply GlobalTheory.ScalTrans.scalar_pair_trans <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericTermsScalarClassesFormFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericTermsScalarClassesFormFamily
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SnFamGen

theorem genFam : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), (∀ t ∈ (Y.tO u u').genSet, ∀ t' ∈ (Y.tO u u').genSet, (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' → (Y.tO u u').s0 t t' = 1 → (Y.tO u u').scal t t' → (Y.tO u u').s0 t' t = 1 ∧ (Y.tO u u').scal t' t) → (∀ t ∈ (Y.tO u u').genSet, ∀ t' ∈ (Y.tO u u').genSet, ∀ t'' ∈ (Y.tO u u').genSet, (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' → (Y.tO u u').rowOf t' = (Y.tO u u').rowOf t'' → (Y.tO u u').s0 t t' = 1 → (Y.tO u u').scal t t' → (Y.tO u u').s0 t' t'' = 1 → (Y.tO u u').scal t' t'' → (Y.tO u u').s0 t t'' = 1 ∧ (Y.tO u u').scal t t'') → FamQ Y u u' Not (Y.tO u u').genSet (gCls Y u u') := by
  intro D X Y u u' hsym htr
  have hG : ∀ t : TauC Y u u', t ∈ (Y.tO u u').genSet → t.G ≠ 0 := by
    intro t ht h0
    have h1 : (Y.tO u u').G t ≠ 0 := ht.1
    apply h1
    show Gt t = 0
    simp [Gt, h0]
  have hrefl : ∀ t : TauC Y u u', t ∈ (Y.tO u u').genSet → t ∈ gCls Y u u' t := by
    intro t ht
    obtain ⟨h1, h2⟩ := GlobalTheory.T.same_row_same_coset_scalar_corank_one D X Y u u' t t (hG t ht) rfl rfl
    exact ⟨ht, rfl, h1, h2⟩

  have hrow : ∀ t t' : TauC Y u u', t' ∈ gCls Y u u' t → (Y.tO u u').rowOf t' = (Y.tO u u').rowOf t :=
    fun t t' h => h.2.1

  have hsub : ∀ t ∈ (Y.tO u u').genSet, ∀ t' ∈ (Y.tO u u').genSet,
      (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' → (Y.tO u u').s0 t t' = 1 → (Y.tO u u').scal t t' →
      gCls Y u u' t' ⊆ gCls Y u u' t := by
    intro t ht t' ht' hr hs hc x hx
    obtain ⟨hxg, hxr, hxs, hxc⟩ := hx
    obtain ⟨h1, h2⟩ := htr t ht t' ht' x hxg hr hxr.symm hs hc hxs hxc
    exact ⟨hxg, hxr.trans hr.symm, h1, h2⟩
  refine ⟨?_, ?_, ?_⟩
  · ext t
    simp [setQ, Formalism.FourierDecayAlt.PB.Terms.genSet]
  · intro t ht t' ht' hn
    constructor
    · intro he
      have : t' ∈ gCls Y u u' t := he ▸ hrefl t' ht'
      exact (hrow t t' this).symm
    · intro hr
      obtain ⟨hs, hc⟩ := GlobalTheory.T.same_row_same_coset_scalar_corank_one D X Y u u' t t' (hG t ht) hr hn
      obtain ⟨hs', hc'⟩ := hsym t ht t' ht' hr hs hc
      exact Set.Subset.antisymm (hsub t' ht' t ht hr.symm hs' hc') (hsub t ht t' ht' hr hs hc)
  · intro t ht t' ht' he
    have : t' ∈ gCls Y u u' t := he ▸ hrefl t' ht'
    exact (hrow t t' this).symm

end GlobalTheory.SnFamGen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericTermsScalarClassesFormFamilyStatement
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericTerms_scalarClasses_form_family : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), (∀ t ∈ (Y.tO u u').genSet, ∀ t' ∈ (Y.tO u u').genSet, (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' → (Y.tO u u').s0 t t' = 1 → (Y.tO u u').scal t t' → (Y.tO u u').s0 t' t = 1 ∧ (Y.tO u u').scal t' t) → (∀ t ∈ (Y.tO u u').genSet, ∀ t' ∈ (Y.tO u u').genSet, ∀ t'' ∈ (Y.tO u u').genSet, (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' → (Y.tO u u').rowOf t' = (Y.tO u u').rowOf t'' → (Y.tO u u').s0 t t' = 1 → (Y.tO u u').scal t t' → (Y.tO u u').s0 t' t'' = 1 → (Y.tO u u').scal t' t'' → (Y.tO u u').s0 t t'' = 1 ∧ (Y.tO u u').scal t t'') → FamQ Y u u' Not (Y.tO u u').genSet (gCls Y u u') := by
  first | exact @GlobalTheory.SnFamGen.genFam | exact GlobalTheory.SnFamGen.genFam | (intros; apply GlobalTheory.SnFamGen.genFam <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CorankOneScalarPairSymmetric
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CorankOneScalarPairSymmetric
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ScalSymm

open Formalism.L2.SG.NGCut

theorem scal_symm : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ t t' : TauC Y u u', t.G ≠ 0 → t'.G ≠ 0 → (Y.tO u u').s0 t t' = 1 → (Y.tO u u').scal t t' → (Y.tO u u').s0 t' t = 1 ∧ (Y.tO u u').scal t' t := by
  intro D X Y u u' t t' hG hG' hs hsc
  have hdim := Formalism.L2.SG.Corank.finrank_VS D
  have hGv : ∀ t : TauC Y u u', t.G ≠ 0 → Gval (lf D (X.Fu u)) t.frame ≠ 0 := fun t h =>
    (Formalism.L2.SG.Pf.SatGram.gterm_G Y t) ▸ h
  have hlat : ∀ t : TauC Y u u', Submodule.IsFullLattice D.host.E t.lam := fun t =>
    ((Y.rowsOK u).1 t.lam t.mem).1.1
  have hLF : ∀ t : TauC Y u u', IsLift t.lam (lf D (X.Fu u)) := fun t =>
    ((Y.rowsOK u).1 t.lam t.mem).2.1.2.2.1
  have hLt : ∀ t : TauC Y u u', IsLift t.lam t.frame := fun t => t.rep.2.2.2.2.1
  obtain ⟨⟨hlam, hlam'⟩, -, hIS⟩ := (show Formalism.L2.SG.TermOp.scalT t t' from hsc)
  have h1' : Formalism.L2.SG.TermOp.s0T t t' = 1 := hs
  unfold Formalism.L2.SG.TermOp.s0T at h1'
  rw [if_pos ⟨hlam, hlam'⟩] at h1'
  have hth := (CorankRelation.s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t.frame t'.frame _ (hLF t) (hLt t)
    (hGv t hG)).1 h1'
  have hL' : IsLift t.lam t'.frame := by rw [hlam]; exact hLt t'
  have hsym := CorankRelation.Th_symm D.R.k hdim t.lam (hlat t) _ t.frame t'.frame (t'.lin * t.lin⁻¹) (hLF t) (hLt t) hL'
    (hGv t hG) (hGv t' hG') (CorankRelation.frame_mem_iff t t') hth
  have hinv : (t'.lin * t.lin⁻¹)⁻¹ = t.lin * t'.lin⁻¹ := by group
  rw [hinv] at hsym
  have hs' : s0 t.lam (lf D (X.Fu u)) t'.frame t.frame (t.lin * t'.lin⁻¹) D.R.k = 1 :=
    (CorankRelation.s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t'.frame t.frame _ (hLF t) hL' (hGv t' hG')).2 hsym
  have hback : ∀ y : (VS D).V, (t'.lin * t.lin⁻¹) ((t.lin * t'.lin⁻¹) y) = y := fun y => by
    show t'.lin (t.lin.symm (t.lin (t'.lin.symm y))) = y
    simp
  refine ⟨?_, ?_⟩
  · show Formalism.L2.SG.TermOp.s0T t' t = 1
    unfold Formalism.L2.SG.TermOp.s0T
    rw [if_pos ⟨hlam.symm, hlam'.symm⟩, ← hlam]
    exact hs'
  · show Formalism.L2.SG.TermOp.scalT t' t
    refine ⟨⟨hlam.symm, hlam'.symm⟩, ?_, ?_⟩
    · rw [← hlam]; exact hs'
    · rw [← hlam]
      intro y2 hy2 y1 hy1 y2'' hy2'' y1' hy1' hd hd' al al'
      have hd1 : y1 - y2 ∈ Xsp (lf D (X.Fu u)) := by
        have := (Xsp (lf D (X.Fu u))).neg_mem hd
        simpa using this
      have hd2 : y2'' - (t'.lin * t.lin⁻¹) y1' ∈ Xsp t'.frame := by
        have h := (CorankRelation.frame_mem_iff t t' _).1 hd'
        rw [map_sub, hback] at h
        have := (Xsp t'.frame).neg_mem h
        simpa using this
      exact (hIS y1 hy1 y2 hy2 y1' hy1' y2'' hy2'' hd1 hd2 al al').symm

end GlobalTheory.ScalSymm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CorankOneScalarPairSymmetricStatement
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.corank_one_scalar_pair_symmetric : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ t t' : TauC Y u u', t.G ≠ 0 → t'.G ≠ 0 → (Y.tO u u').s0 t t' = 1 → (Y.tO u u').scal t t' → (Y.tO u u').s0 t' t = 1 ∧ (Y.tO u u').scal t' t := by
  first | exact @GlobalTheory.ScalSymm.scal_symm | exact GlobalTheory.ScalSymm.scal_symm | (intros; apply GlobalTheory.ScalSymm.scal_symm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericScalarClassTermsFormFamily
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SnFamGenAll

theorem famGen : GlobalTheory.SnFam.FamGen := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, ?_⟩
  intro C' Cl _ _ D large₂ X Y u u' _
  have hG : ∀ t : TauC Y u u', t ∈ (Y.tO u u').genSet → t.G ≠ 0 := by
    intro t ht h0
    have h1 : (Y.tO u u').G t ≠ 0 := ht.1
    apply h1
    show Gt t = 0
    simp [Gt, h0]
  exact GlobalTheory.T.genericTerms_scalarClasses_form_family D X Y u u'
    (fun t ht t' ht' _ hs hc => GlobalTheory.T.corank_one_scalar_pair_symmetric D X Y u u' t t' (hG t ht) (hG t' ht') hs hc)
    (fun t ht t' ht' t'' ht'' _ _ hs hc hs' hc' =>
      GlobalTheory.T.scalarCorankOnePairs_trans D X Y u u' t t' t'' (hG t ht) (hG t' ht') (hG t'' ht'') hs hc hs' hc')

end GlobalTheory.SnFamGenAll
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericScalarClassTermsFormFamilyStatement
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericScalarClassTerms_formFamily : GlobalTheory.SnFam.FamGen := by
  first | exact @GlobalTheory.SnFamGenAll.famGen | exact GlobalTheory.SnFamGenAll.famGen | (intros; apply GlobalTheory.SnFamGenAll.famGen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericFamilyStepOfSiegelWeil
open GlobalTheory.SnFam

namespace GlobalTheory.SnFamTop

theorem stepFamG_of_SWXS (hSW : PI.VolStabS.MassDataS.SWXS) :
    Formalism.L2.SG.Pf.MainEqFam.StepFamG :=
  GlobalTheory.T.genericRow_familyStep_of_leaves
    (fun D h F _ _ _ E _ _ _ _ M hM V _ _ H hV P hP R d0 h0 d t ht Y0 hZ =>
      GlobalTheory.mass_pairingClass_bounds M hM H _ _ P h hV hP R d0 h0 d t ht Y0 _ rfl hZ _ rfl)
    GlobalTheory.T.differentLocalIdentity_familiesLemmaH GlobalTheory.T.genericScalarClassTerms_formFamily GlobalTheory.T.familyRowWeightSumUnfoldingIdentity (GlobalTheory.T.familyGenericMassPositiveBounded_proof hSW) GlobalTheory.T.familyGroupSumFactorsRowWeightAmplitude_proof GlobalTheory.T.familyLocalObjectsExistAtTerms_proof

end GlobalTheory.SnFamTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericFamilyStepOfSiegelWeilStatement
open GlobalTheory.SnFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericFamilyStep_of_siegelWeil : PI.VolStabS.MassDataS.SWXS → Formalism.L2.SG.Pf.MainEqFam.StepFamG := by
  first | exact @GlobalTheory.SnFamTop.stepFamG_of_SWXS | exact GlobalTheory.SnFamTop.stepFamG_of_SWXS | (intros; apply GlobalTheory.SnFamTop.stepFamG_of_SWXS <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalCountGenericRow
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalCountGenericRow
open Formalism.L2.SG.Pf.MainEqSteps

namespace GlobalTheory

theorem stepNormalsG_holds : StepNormalsG :=
  Formalism.L2.SG.NGCut.NormalInvariants.Gen.stepNormalsG_of
    (Formalism.L2.SG.Pf.nmlInvG_of Formalism.L2.SG.NGCut.NormalVectorPairings.NmlLine_holds
      Formalism.L2.SG.NGCut.NormalIntegrality.NmlInt_holds Formalism.L2.SG.NGCut.NormalVectorPairings.NmlSep_holds)
    Formalism.L2.SG.NGCut.NormalCount.NormCount_holds
    GlobalTheory.T.equalWords_nonGeneric_estimates_chain.2.2.2.1

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalCountGenericRowStatement
open Formalism.L2.SG.Pf.MainEqSteps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalCount_genericRow : StepNormalsG := by
  first | exact @GlobalTheory.stepNormalsG_holds | exact GlobalTheory.stepNormalsG_holds | (intros; apply GlobalTheory.stepNormalsG_holds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EqualWordGenericBoundOfNormalisedSteps
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericHeightBoundOfLocalEstimates
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericHeightBoundOfLocalEstimates
noncomputable section

open scoped Classical
open Formalism.FourierDecayAlt Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna GlobalTheory.SnPos

namespace GlobalTheory.SnPos

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem genCutP_of_steps (hS : StepSizes) (hC : StepClassG) (hN : StepNormalsG) (hP : StepPointsG)
    (hH : StepHeightG) (hA : StepAnalyticGP) : GenCutP := by
  intro Cg cb Cw cT CT C0 A0 hcb hcT
  obtain ⟨C1, C0n, hA1⟩ := hA Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨CB, CSt, hCB, hCSt, a₀, b₀, hA2⟩ := hA1 (C1 + C0n + 38)
  obtain ⟨Cgs, CTs, hCg, hCT, s₀, t₀, hS2⟩ := hS Cg cb Cw cT CT C0
  obtain ⟨n₀, m₀, hN2⟩ := hN Cg cb Cw cT CT C0
  obtain ⟨p₀, q₀, hP2⟩ := hP Cg cb Cw cT CT C0
  obtain ⟨h₀, j₀, hH2⟩ := hH Cg cb Cw cT CT C0
  refine ⟨C1, C0n, C1 + C0n + 38, CB, CSt, Cgs, CTs, hCB, hCSt, hCg, hCT, le_refl _,
    max a₀ (max s₀ (max n₀ (max p₀ h₀))), max b₀ (max t₀ (max m₀ (max q₀ j₀))),
    fun C' Cl h1 h2 D large₂ X Y u hTies hHy hT => ?_⟩
  have hc : Formalism.L2.SG.NGCut.Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u := ⟨hHy.1, hHy.2.1, hT⟩
  have e1' : a₀ ≤ C' := le_trans (le_max_left _ _) h1
  have e2' : b₀ ≤ Cl := le_trans (le_max_left _ _) h2
  have f1 : s₀ ≤ C' := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) h1
  have f2 : t₀ ≤ Cl := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) h2
  have i1 : n₀ ≤ C' :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) h1
  have i2 : m₀ ≤ Cl :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) h2
  have j1 : p₀ ≤ C' := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) h1
  have j2 : q₀ ≤ Cl := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) h2
  have k1 : h₀ ≤ C' := le_trans (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) h1
  have k2 : j₀ ≤ Cl := le_trans (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) h2
  obtain ⟨P, iP, B, Irat, Ire, νL, νB, ng, cSt, e1, hBk, hL, hBq, c1, c2, c3, c4, hV, hLoc, hGen, hMeas, hSum⟩ :=
    hA2 C' Cl e1' e2' D large₂ X Y u hTies hc
  obtain ⟨hG, hdd, hNI, hFI⟩ := hBk
  refine ⟨P, iP, B, cSt, e1, Irat, Ire, νL, νB, ng, hL, hBq, hG, hdd, hNI, hFI,
    Formalism.L2.SG.NGCut.ngSizes_of (hS2 C' Cl f1 f2 D large₂ X Y u u hc) c1 c2 c3 c4, ?_⟩
  exact ⟨classInputG_of Y u (hC D X Y u (g_ge_three hc) hT) νL νB ng, ampInputG_of_vanish Y u νL νB ng hV,
    hN2 C' Cl i1 i2 D large₂ X Y u hc νL νB ng, hP2 C' Cl j1 j2 D large₂ X Y u hc νL νB ng, hLoc, hMeas, hGen,
    hH2 C' Cl k1 k2 D large₂ X Y u hc νL νB ng, hSum⟩

end GlobalTheory.SnPos
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericHeightBoundOfLocalEstimatesStatement
open Formalism.FourierDecayAlt Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna GlobalTheory.SnPos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_height_bound_of_local_estimates : StepSizes → StepClassG → StepNormalsG → StepPointsG → StepHeightG → StepAnalyticGP → GenCutP := by
  first | exact @GlobalTheory.SnPos.genCutP_of_steps | exact GlobalTheory.SnPos.genCutP_of_steps | (intros; apply GlobalTheory.SnPos.genCutP_of_steps <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AnalyticConstantGenericBoundOfNormalisedSteps
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AnalyticConstantGenericBoundOfNormalisedSteps
open Formalism.FourierDecayAlt Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna GlobalTheory.SnPos

noncomputable section

open scoped Classical

namespace GlobalTheory.SnPos

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem stepAnalyticCGP_of_steps : StepPinExists → StepTermVanishG → StepLocGenPinnedG → StepThmBGP →
    StepAnalyticCGP := by
  intro hE hV hL hB Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨C1, C0n, CSt, hCSt, a₀, b₀, hL2⟩ := hL Cg cb Cw cT CT C0
  obtain ⟨e₀, f₀, hE2⟩ := hE Cg cb Cw cT CT C0
  obtain ⟨v₀, w₀, hV2⟩ := hV Cg cb Cw cT CT C0
  refine ⟨C1, C0n, fun A => ?_⟩
  obtain ⟨CB, hCB, p₀, q₀, hB2⟩ := hB Cg cb Cw cT CT C0 hcb hcT A
  refine ⟨CB, CSt, hCB, hCSt, max a₀ (max e₀ (max v₀ p₀)), max b₀ (max f₀ (max w₀ q₀)),
    fun C' Cl h1 h2 D large₂ X Y u hTi hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hBk => ?_⟩
  have ha1 : a₀ ≤ C' := le_trans (by simp) h1
  have ha2 : b₀ ≤ Cl := le_trans (by simp) h2
  have he1 : e₀ ≤ C' := le_trans (by simp) h1
  have he2 : f₀ ≤ Cl := le_trans (by simp) h2
  have hv1 : v₀ ≤ C' := le_trans (by simp) h1
  have hv2 : w₀ ≤ Cl := le_trans (by simp) h2
  have hp1 : p₀ ≤ C' := le_trans (by simp) h1
  have hp2 : q₀ ≤ Cl := le_trans (by simp) h2
  obtain ⟨ν, hν⟩ := hE2 C' Cl he1 he2 D large₂ X Y u u hc
  obtain ⟨s, ng, e1, hs1, hs0, hsb, he0, he3, hLoc, hGen⟩ :=
    hL2 C' Cl ha1 ha2 D large₂ X Y u hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hBk ν hν
  have hb0 : 0 ≤ large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f) :=
    le_trans (sq_nonneg _) (hsb 1)
  exact ⟨sc s ν, ν, ng, large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f), e1,
    Formalism.L2.SG.NGAnalytic.nuQOK_sc u u s hs1 hs0 ν hν.1, hν.1, hb0, le_rfl, he0, he3,
    ampVanishG_sc Y u s hs0 ν (ampVanishG_of_term Y u ν (hV2 C' Cl hv1 hv2 D large₂ X Y u hc ν hν)), hLoc, hGen,
    measureInputG_sc Y u s ν _ hsb ng,
    hB2 C' Cl hp1 hp2 D large₂ X Y u hTi hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hBk ν hν (sc s ν) ng⟩

end GlobalTheory.SnPos
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AnalyticConstantGenericBoundOfNormalisedStepsStatement
open Formalism.FourierDecayAlt Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna GlobalTheory.SnPos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analyticConstantGenericBound_of_normalisedSteps : StepPinExists → StepTermVanishG → StepLocGenPinnedG → StepThmBGP → StepAnalyticCGP := by
  first | exact @GlobalTheory.SnPos.stepAnalyticCGP_of_steps | exact GlobalTheory.SnPos.stepAnalyticCGP_of_steps | (intros; apply GlobalTheory.SnPos.stepAnalyticCGP_of_steps <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EqualWordGenericBoundOfCutBoundPositive
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EqualWordGenericBoundOfCutBoundPositive
open Formalism.FourierDecayAlt Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna GlobalTheory.SnPos

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData

namespace GlobalTheory.SnPos

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rowMainEqP_of_cut (hCh : PN.NGChain) (hMG : MeanAmpGen) (hc : GenCutP) : RowMainEqP := by
  intro Cg cb Cw cT CT C0 A hcb hcT
  obtain ⟨C1, C0n, Aexp, CB, CSt, Cgs, CTs, h1, h2, h3, h4, hA, C'₀, Cl₀, h⟩ := hc Cg cb Cw cT CT C0 A hcb hcT
  obtain ⟨Cn, hCn, hK⟩ := rowGenJoint_of hCh hMG C1 C0n Aexp CB CSt Cgs CTs h1 h2 h3 h4 hA
  refine ⟨Cn, hCn, C'₀, Cl₀, fun C' Cl a b D large₂ X Y u hTies hH hT ha => ?_⟩
  obtain ⟨P, iP, B, cSt, e1, Irat, Ire, νL, νB, ng, _, _, hG, hdd, hN, hF, hS, hIn⟩ :=
    h C' Cl a b D large₂ X Y u hTies hH hT
  have hcard := Formalism.MainNotions.LatticeGluingRadicals.d_card D
  have key := hK D.host.E (TauC Y u u) _ _ _ _ (Y.tO u u) D.R.rS D.R.k (Set (TauC Y u u)) (NuC D)
    (NOfG Y u νL νB ng) P B large₂.sc.b (2 * D.host.v) (X.B.g : ℝ) (((Tu D u : ℕ) : ℝ) * ((Tu D u : ℕ) : ℝ))
    cSt e1 Irat Ire
  rw [hcard] at key
  have r := key ha hG hN hF hS hIn
  rw [hdd] at r
  exact r

end GlobalTheory.SnPos
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EqualWordGenericBoundOfCutBoundPositiveStatement
open Formalism.FourierDecayAlt Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna GlobalTheory.SnPos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equalWordGenericBound_of_cutBound_positive : PN.NGChain → MeanAmpGen → GenCutP → GlobalTheory.SnPos.RowMainEqP := by
  first | exact @GlobalTheory.SnPos.rowMainEqP_of_cut | exact GlobalTheory.SnPos.rowMainEqP_of_cut | (intros; apply GlobalTheory.SnPos.rowMainEqP_of_cut <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AnalyticGenericBoundOfChoiceStepPositive
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AnalyticGenericBoundOfChoiceStepPositive
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic
  Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna GlobalTheory.SnPos

namespace GlobalTheory.SnPos

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem stepAnalyticGP_of (hTi : TieOfCtx) (hB : StepChoiceConstantsC) (hA : StepAnalyticCGP) : StepAnalyticGP := by
  intro Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨C1, C0n, hA1⟩ := hA Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨k₀, l₀, hB2⟩ := hB Cg cb Cw cT CT C0
  obtain ⟨m₀, n₀, hT2⟩ := hTi Cg cb Cw cT CT C0
  refine ⟨C1, C0n, fun A => ?_⟩
  obtain ⟨CB, CSt, h1, h2, a₀, b₀, hA2⟩ := hA1 A
  refine ⟨CB, CSt, h1, h2, max a₀ (max k₀ m₀), max b₀ (max l₀ n₀), fun C' Cl e1 e2 D large₂ X Y u hD hc => ?_⟩
  obtain ⟨hb, X0, ψ, hT⟩ := hT2 C' Cl (le_trans (by simp) e1) (le_trans (by simp) e2) D large₂ X Y u u hc
  obtain ⟨sd, C, Th, F0, what₂, vR, Q, i0, i0', νq, Irat, Ire, hBk⟩ :=
    hB2 C' Cl (le_trans (by simp) e1) (le_trans (by simp) e2) D large₂ X Y u u hc hb X0 ψ hT
  have hBk' := massDataValid_unscale (kapU_pos D) hBk
  obtain ⟨νL, νB, ng, cSt, e, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ :=
    hA2 C' Cl (le_trans (by simp) e1) (le_trans (by simp) e2) D large₂ X Y u hD hc hb X0 ψ hT sd C Th
      F0 what₂ vR Q i0 i0' νq (Irat * kapU D) (Ire * kapU D) hBk'
  exact ⟨_, inferInstance, _, Irat * kapU D, Ire * kapU D, νL, νB, ng, cSt, e, hBk', a1, a2, a3, a4, a5, a6, a7,
    a8, a9, a10, a11⟩

end GlobalTheory.SnPos
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AnalyticGenericBoundOfChoiceStepPositiveStatement
open Formalism.FourierDecayAlt Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna GlobalTheory.SnPos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analyticGenericBound_of_choiceStep_positive : TieOfCtx → StepChoiceConstantsC → StepAnalyticCGP → StepAnalyticGP := by
  first | exact @GlobalTheory.SnPos.stepAnalyticGP_of | exact GlobalTheory.SnPos.stepAnalyticGP_of | (intros; apply GlobalTheory.SnPos.stepAnalyticGP_of <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EqualWordGenericBoundOfNormalisedSteps
open Formalism.FourierDecayAlt Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna GlobalTheory.SnPos

namespace GlobalTheory.SnPos

theorem rowMainEqP_of_pinned (hCh : PN.NGChain) (hC : StepClassG) (hN : StepNormalsG) (hP : StepPointsG)
    (hO : StepNormOneG) (hTi : TieOfCtx) (hB : StepChoiceConstantsC) (hE : StepPinExists) (hV : StepTermVanishG)
    (hL : StepLocGenPinnedG) (hT : StepThmBGP) : GlobalTheory.SnPos.RowMainEqP :=
  GlobalTheory.T.equalWordGenericBound_of_cutBound_positive hCh Formalism.L2.SG.Pf.MainEqCut.meanAmplitudeGeneric_holds
    (GlobalTheory.T.generic_height_bound_of_local_estimates Formalism.L2.SG.NGCut.sizes_of_hypotheses hC hN hP (stepHeightG_of_normOne hO)
      (GlobalTheory.T.analyticGenericBound_of_choiceStep_positive hTi hB (GlobalTheory.T.analyticConstantGenericBound_of_normalisedSteps hE hV hL hT)))

end GlobalTheory.SnPos
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EqualWordGenericBoundOfNormalisedStepsStatement
open Formalism.FourierDecayAlt Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna GlobalTheory.SnPos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equalWordGenericBound_of_normalisedSteps : PN.NGChain → StepClassG → StepNormalsG → StepPointsG → StepNormOneG → TieOfCtx → StepChoiceConstantsC → StepPinExists → StepTermVanishG → StepLocGenPinnedG → StepThmBGP → GlobalTheory.SnPos.RowMainEqP := by
  first | exact @GlobalTheory.SnPos.rowMainEqP_of_pinned | exact GlobalTheory.SnPos.rowMainEqP_of_pinned | (intros; apply GlobalTheory.SnPos.rowMainEqP_of_pinned <;> assumption)
end
end

namespace GlobalTheory

theorem rowMainEqP_of_siegelWeil_of_stepChoice :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → Formalism.L2.SG.NGAnalytic.StepChoiceConstantsC →
      Formalism.L2.SG.Pf.BDat.StepThmBG → Formalism.L2.SG.RowsPos.RowMainEqP := by
  intro h hB hT
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, _h8, h9⟩ := GlobalTheory.T.equalWords_nonGeneric_estimates_chain
  refine GlobalTheory.T.equalWordGenericBound_of_normalisedSteps h1 h2 GlobalTheory.T.normalCount_genericRow h3 h4 h5 hB h6 h7 (h9 (GlobalTheory.T.genericFamilyStep_of_siegelWeil (GlobalTheory.St.swxs_of_siegelWeil h))) ?_
  intro Cg cb Cw cT CT C0 _ _ A
  obtain ⟨CB, h0, a, b, H⟩ := hT Cg cb Cw cT CT C0 A
  exact ⟨CB, h0, a, b, fun C' Cl h1 h2 D large₂ X Y u _ => H C' Cl h1 h2 D large₂ X Y u⟩

end GlobalTheory
end

namespace GlobalTheory

theorem rowMainEqP_of_siegelWeil :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → Formalism.L2.SG.RowsPos.RowMainEqP :=
  fun h => GlobalTheory.rowMainEqP_of_siegelWeil_of_stepChoice h
    (GlobalTheory.St.stepChoiceDataC_of_siegelWeil_inInfinity h
      (fun _ X u u' hg => Formalism.L2.SG.RealObj.EnergyConvJ.BM.realObj_inInfinityX_jsz
        CompanionTheory.Lime.BM.uniqGap_holds hg X u u' 1 one_pos))
    Formalism.MainStatements.RowRest.bDat_theoremB_global

end GlobalTheory
