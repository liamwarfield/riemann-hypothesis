module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqWire
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXVolH
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.WeightConstT
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBCovN

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.MassDataPosAllOf
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXCovolPos
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXRecPos
noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets

namespace Formalism.L2.SG.Pf.MassDataX

theorem massH_pos {D : D7} (X : HidaSetting D) (u : D.what₂.Word) :
    0 < massH X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) (frameOf X u) := by
  classical
  have hC := Formalism.L2.SG.Pf.MassDataX.classFinite_holds X u
  have hS := MassDataMassesW.stabFinite_of Formalism.L2.SG.Pf.MassDataX.hinfCompact_holds
    Formalism.L2.SG.Pf.MassDataX.kCompactOpen_holds X u
  show 0 < massCl (MassDataMassesW.GamH X u) (MassDataMassesW.KH X u)
  unfold massCl
  haveI := hC
  letI : Fintype (DoubleCoset.Quotient (G := ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)))
      (MassDataMassesW.GamH X u : Set ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)))
      (MassDataMassesW.KH X u : Set ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)))) :=
    Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  apply Finset.sum_pos
  · intro c _
    haveI := hS (Quotient.out c)
    apply inv_pos.mpr
    exact_mod_cast Nat.card_pos
  · exact Finset.univ_nonempty_iff.mpr ⟨Quot.mk _ 1⟩

theorem finrank_Vpi_pos {D : D7} (X : HidaSetting D) (u : D.what₂.Word) : 0 < Module.finrank ℂ (X.Vpi u) := by
  classical
  have hx : ∀ v, ∃ y : X.Vloc u v, y ≠ 0 := fun v => by
    haveI := (X.piLoc_type u v).1
    exact exists_ne 0
  choose x hx using hx
  have hne : X.tensU u x ≠ 0 := by
    intro h0
    have h := X.tensU_inner u x x
    rw [h0, inner_zero_left] at h
    exact (Finset.prod_ne_zero_iff.mpr fun v _ => inner_self_ne_zero.mpr (hx v)) h.symm
  exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, hne⟩

end Formalism.L2.SG.Pf.MassDataX
end
end

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Volumes

namespace Formalism.L2.SG.Pf.MassDataX

theorem covolH_pos {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (w : D.what₂.Word) (hT : X.MeasTie hb) :
    0 < covol (X.measW w).μH := by
  have hM : massH X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) (frameOf X w) =
      covol (X.measW w).μH / ((X.muH w Set.univ).toReal *
        ((X.measW w).μHf (Subtype.val ⁻¹' (MassDataMassesW.KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)))).toReal) :=
    MassDataMassesW.massAll_of hinfCompact_holds kCompactOpen_holds classFinite_holds X hb w hT
  have hm := massH_pos X w
  rw [hM] at hm
  rcases div_pos_iff.mp hm with h | h
  · exact h.1
  · exact absurd h.2 (not_lt.mpr (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg))

theorem volH_pos {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (w : D.what₂.Word) (hT : X.MeasTie hb) :
    0 < (X.muH w Set.univ).toReal := by
  have hM : massH X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) (frameOf X w) =
      covol (X.measW w).μH / ((X.muH w Set.univ).toReal *
        ((X.measW w).μHf (Subtype.val ⁻¹' (MassDataMassesW.KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)))).toReal) :=
    MassDataMassesW.massAll_of hinfCompact_holds kCompactOpen_holds classFinite_holds X hb w hT
  have hm := massH_pos X w
  rw [hM] at hm
  have h0 : (X.muH w Set.univ).toReal *
      ((X.measW w).μHf (Subtype.val ⁻¹' (MassDataMassesW.KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)))).toReal ≠ 0 := by
    intro h
    rw [h, div_zero] at hm
    exact lt_irrefl _ hm
  exact lt_of_le_of_ne ENNReal.toReal_nonneg (fun h => h0 (by rw [← h, zero_mul]))

theorem muHpp_pos {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (w : D.what₂.Word) :
    0 < ((X.measW w).μHf (Subtype.val ⁻¹' K2u X hb w)).toReal := by
  haveI hHaar : (X.measW w).μHf.IsHaarMeasure := (X.measW_norm w).2.2.1
  obtain ⟨hO, h1, hsub⟩ := conjugated_level_open_one_mem (X := X) (hb := hb) (hK := hK) (u := w)
  have hHc := (closed_SNH_X (X := X) (u := w)).2.2
  have hKc := hHc.isClosedEmbedding_subtypeVal.isCompact_preimage (kCompactOpen_holds X).1
  have hKf : (X.measW w).μHf (Subtype.val ⁻¹' (MassDataMassesW.KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J))) < ⊤ := by
    exact hHaar.toIsFiniteMeasureOnCompacts.lt_top_of_isCompact hKc
  have hfin : (X.measW w).μHf (Subtype.val ⁻¹' K2u X hb w) < ⊤ :=
    lt_of_le_of_lt (measure_mono (Set.preimage_mono hsub)) hKf
  have hpos : (X.measW w).μHf (Subtype.val ⁻¹' K2u X hb w) ≠ 0 :=
    ((hO.preimage continuous_subtype_val).measure_pos _ ⟨1, h1⟩).ne'
  exact ENNReal.toReal_pos hpos hfin.ne

section Main

open Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.MassDataConc Formalism.L2.SG.Pf.MassDataPos

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

theorem covolPosC_of (hSW : PI.VolStabS.MassDataS.SWXS) (hψ : IsCharAF X.B.I.F ψ) (hC : MeasCompatψ X ψ)
    (hT : X.MeasTie hb) (hdet : (gramE X.B.I.cm.sig X.B.I.J X0).det ≠ 0) :
    CovolPosC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq := by
  have hs := MassDataVolumesW.stepSizeW X
  have hH := covolH_pos X hb u hT
  have hH' := covolH_pos X hb u' hT
  have hG : 0 < covolBy (G := HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J) (HFinIn (AF X.B.I.F) X.B.I.cm.sig X.B.I.J)
      X.measG.μG := by
    rw [← covolH_eq_volG hSW X ψ hψ hC u]; exact hH
  obtain ⟨hTB, νB, hνB, hcB⟩ := hC.2 X0 hdet
  have eB := MassDataVolumesW.covol_eq_covolBy_w (PI.VolStabS.MassDataS.volStabXS_of hSW X) (MassDataVolumesW.stepHerm X)
    (a := 2 * D.R.rS + 2) (by omega) (by omega) X0 hTB hdet hψ X.measG_norm.1 hνB (X.measG_norm.2.2.2.2.1 X0) hcB
  refine ⟨hG, hH, hH', ?_, ?_, ?_⟩
  · show 0 < covol (X.measW u).μN
    rw [(hC.1 u).2]; exact one_pos
  · show 0 < covol (X.measW u').μN
    rw [(hC.1 u').2]; exact one_pos
  · show 0 < covol (X.measG.μB X0)
    rw [eB]; exact hG

end Main

end Formalism.L2.SG.Pf.MassDataX
end
end

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.MassDataX

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.MassDataConc Formalism.L2.SG.Pf.MassDataPos Formalism.L2.SG.TypedSets

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def DvPosC : Prop := ∀ {D : D7} (X : HidaSetting D) (v : NumberField.InfinitePlace X.B.I.F), 0 < X.dv v

theorem recPosC_of_dv {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
    (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
    {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
    {F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
    (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (hDv : DvPosC) (hX : HypX X hb FdN FdN' u u') :
    RecPosC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq := by
  have hTie := hX.1
  have hcol := (inColumnsAt_holds X hb hK FdN FdN' u u' X0 (Formalism.L2.SG.LocVol.locOf X u u' ψ)
    ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ hX)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show 0 < Formalism.L2.SG.RealObj.degX X
    unfold Formalism.L2.SG.RealObj.degX
    exact Finset.prod_pos fun v _ => hDv X v
  · exact Nat.cast_pos.mpr (finrank_Vpi_pos X u)
  · exact Nat.cast_pos.mpr (finrank_Vpi_pos X u')
  · exact massH_pos X u
  · exact massH_pos X u'
  · show (0 : ℝ) < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).d
    rw [show (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).d = _ from hcol.1]
    exact mul_pos (Nat.cast_pos.mpr (finrank_Vpi_pos X u))
      (div_pos (covolH_pos X hb u hTie) (mul_pos (volH_pos X hb u hTie) (muHpp_pos X hb hK u)))
  · show (0 : ℝ) < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).d'
    rw [show (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).d' = _ from hcol.2.2.1]
    exact mul_pos (Nat.cast_pos.mpr (finrank_Vpi_pos X u'))
      (div_pos (covolH_pos X hb u' hTie) (mul_pos (volH_pos X hb u' hTie) (muHpp_pos X hb hK u')))

end Formalism.L2.SG.Pf.MassDataX

namespace Formalism.L2.SG.PoincareAmplitudeLowerBounds

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
open Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups ValuativeRel Formalism.L2.SG.SpectralTiesReal
open Formalism.L2.SG.DataInst Formalism.L2.SG.CntLocal Formalism.L2.SG.RowsConc Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def DensNonnegAll : Prop :=
  ∀ (D : D7) (T : STies D) (u u' : D.what₂.Word) (Lsp : LocSp D T.Y.M) (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]),
    0 ≤ supDens Lsp T.Y.δ ϖ u u' (T.X.Fu u) (T.Y.what₂ u) / ∏' p, alpD u u' p

theorem massDataPosAll_of (hP : ProdConvAll) (hSW : PI.VolStabS.MassDataS.SWXS) (hDv : Formalism.L2.SG.Pf.MassDataX.DvPosC)
    (hDN : DensNonnegAll) : MassDataPosAll := by
  intro D T u u' X0 C Th Q i0 i0' νq Lsp ϖ hne hst hCT hdet hC hTh _
  have hK : T.X.LevelSubgroupNormalized := hCT.1
  have hV : 0 < T.X.volK2 := ENNReal.toReal_pos hK.2.2.1.ne' hK.2.2.2.ne
  have hX : Formalism.L2.SG.TypedSets.HypX T.X T.hb (T.Y.FN u) (T.Y.FN u') u u' :=
    ⟨T.measTie, hK, T.Y.FN_fund u, T.Y.FN_fund u'⟩
  exact Formalism.L2.SG.Pf.MassDataPos.massDataPosC_of (hL := Formalism.L2.SG.Pf.MassDataX.locHaarPosC_holds ..)
    (hCv := Formalism.L2.SG.Pf.MassDataX.covolPosC_of (hSW := hSW) (hψ := T.ψ_char) (hC := T.measCompat)
      (hT := T.measTie) (hdet := hdet) ..)
    (hQv := Formalism.L2.SG.Pf.MassDataPos.quotVolPosC_of T.X T.hb T.Y u u' X0 T.ψ _ _ C Th _ Q _ _ i0 i0' νq hK hV)
    (hR := Formalism.L2.SG.Pf.MassDataX.recPosC_of_dv T.X T.hb T.Y.hK _ _ u u' X0 T.ψ _ _ C Th _ Q _ _ i0 i0' νq hDv hX)
    (hP := hP D T u u' hne hst) (hCoo := Formalism.L2.SG.Pf.MassDataPos.cooOf_pos T.X u u')
    (hκ := Formalism.L2.SG.WConst.kapN_pos) (hsd := hDN D T u u' Lsp ϖ) (hC := hC) (hTh := hTh) ..

end Formalism.L2.SG.PoincareAmplitudeLowerBounds
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.StandardCoordinates
noncomputable section

open scoped Classical
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

namespace Formalism.L2.SG.StandardCoordinates

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} (v : InfinitePlace X.B.I.F) {lam : ℂ} (hl : lam ≠ 0)
  {Q : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ} {Qi : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ}
  (hT : IsTranspC X v lam D.R.k D.R.rS Q Qi) (u' : D.what₂.Word)


include hT in
theorem fam_eq (hl : lam ≠ 0) (b : Fin (D.R.rS + 1)) :
    Formalism.L2.SG.RealObj.frm X u' 1 v b =
      (lam ^ (D.R.rS - b.val))⁻¹ • (Q *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u')) b) := by
  unfold Formalism.L2.SG.RealObj.frm Formalism.L2.SG.RealObj.famSc Formalism.L2.SG.RealObj.fam
  simp only [Complex.ofReal_one, one_pow, inv_one, one_smul]
  refine Fin.lastCases ?_ (fun c => ?_) b
  · rw [Fin.snoc_last]
    unfold Formalism.QuantumDeterminants.fvec
    rw [dite_eq_right (by simp), Matrix.mulVec_mulVec, hT.2.1, Matrix.one_mulVec, Fin.val_last, Nat.sub_self, pow_zero,
      inv_one, one_smul]
  · rw [Fin.snoc_castSucc]
    have h1 := (hT.2.2.2 c c rfl).1
    unfold Formalism.QuantumDeterminants.fvec Formalism.QuantumDeterminants.bvec
    simp only [Fin.coe_castSucc, Fin.is_lt, dif_pos, Fin.eta]
    rw [h1, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hl), one_smul]


include hT hl in
theorem stCoordV_gen (w : Point D.host.E (D.R.rS + 1)) (γ : X.B.I.Ginf) (y : Formalism.REAL.UJ (X.B.I.ε v))
    (p : Formalism.L2.SG.RealObj.FreeE w) :
    Formalism.L2.SG.NGPin.stCoordV X u' w γ v y p =
      ((D.host.rdE : ℂ) * lam) ^ (D.R.rS - p.1.1.1) / ((D.host.rdE : ℂ) * lam) ^ (D.R.rS - p.1.2.1) *
      ((Qi * uMat ((γ v)⁻¹ * y * γ v) * Q) *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u')) p.1.2)
        (Formalism.QuantumDeterminants.eI D.R.k D.R.rS ⟨p.1.1.1, by have := p.2.1; have := p.1.2.isLt; omega⟩) := by
  have hQQi := hT.2.1
  have hH := hT.2.2.1
  have ha : p.1.1.1 < D.R.rS := by have := p.2.1; have := p.1.2.isLt; omega
  have hrd : (D.host.rdE : ℂ) ≠ 0 := by
    have := Formalism.L2.SG.RealFrameCoordinates.frS_mul_rd D
    intro h; rw [h, mul_zero] at this; exact zero_ne_one this
  set z' := Qi *ᵥ rv X.B.I v (X.zR u') with hz'
  set f := Formalism.QuantumDeterminants.fvec D.R.k D.R.rS z' p.1.2 with hf
  have hfrm : Formalism.L2.SG.RealObj.frm X u' D.host.rdE v p.1.2 =
      ((D.host.rdE : ℂ) ^ (D.R.rS - p.1.2.val))⁻¹ • ((lam ^ (D.R.rS - p.1.2.val))⁻¹ • (Q *ᵥ f)) := by
    rw [← fam_eq v hT u' hl p.1.2]
    unfold Formalism.L2.SG.RealObj.frm Formalism.L2.SG.RealObj.famSc
    simp only [Complex.ofReal_one, one_pow, inv_one, one_smul]
  have hfR : rv X.B.I v (X.fR ⟨p.1.1.1, ha⟩) =
      star (lam ^ (D.R.rS - p.1.1.1)) • (Q *ᵥ Pi.single (Formalism.QuantumDeterminants.esI D.R.k D.R.rS ⟨p.1.1.1, ha⟩) 1) := by
    rw [(hT.2.2.2 ⟨p.1.1.1, ha⟩ ⟨p.1.1.1, ha⟩ rfl).2, smul_smul, mul_inv_cancel₀, one_smul]
    exact star_ne_zero.2 (pow_ne_zero _ hl)
  have hM : uMat ((γ v)⁻¹ * y * γ v) *ᵥ (Q *ᵥ f) = Q *ᵥ ((Qi * uMat ((γ v)⁻¹ * y * γ v) * Q) *ᵥ f) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    congr 1
    rw [← Matrix.mul_assoc Q, ← Matrix.mul_assoc Q, hQQi, Matrix.one_mul]
  have hQ : ∀ x v' : Fin (2 * D.R.rS + D.R.k + 1) → ℂ,
      star (Q *ᵥ x) ⬝ᵥ (Formalism.REAL.Jm (X.B.I.ε v) *ᵥ (Q *ᵥ v')) = star x ⬝ᵥ (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS *ᵥ v') := by
    intro x v'
    rw [← Formalism.L2.SG.Pf.LTL.star_dot_conjT, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hH]
  unfold Formalism.L2.SG.NGPin.stCoordV
  rw [hfrm, hfR, Matrix.mulVec_smul, Matrix.mulVec_smul, hM]
  unfold hJ
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, dotProduct_smul, dotProduct_smul, star_smul, smul_dotProduct, hQ,
    Pi.star_single, star_one, single_dotProduct, one_mul, Formalism.L2.SG.RealFrameCoordinates.hpk_esI]
  simp only [smul_eq_mul, star_star]
  have h1 : (lam ^ (D.R.rS - p.1.2.val)) ≠ 0 := pow_ne_zero _ hl
  have h2 : ((D.host.rdE : ℂ) ^ (D.R.rS - p.1.2.val)) ≠ 0 := pow_ne_zero _ hrd
  rw [mul_pow, mul_pow]
  field_simp


include hT hl in
theorem coord_conj (M H : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)
    (hHU : Hᴴ * Formalism.REAL.Jm (X.B.I.ε v) * H = Formalism.REAL.Jm (X.B.I.ε v)) (hHu : IsUnit H.det)
    (he : ∀ b, H *ᵥ rv X.B.I v (X.eR b) = rv X.B.I v (X.eR b)) (hz : H *ᵥ rv X.B.I v (X.zR u') = rv X.B.I v (X.zR u'))
    (hfa : ∀ a, H *ᵥ rv X.B.I v (X.fR a) = rv X.B.I v (X.fR a)) (a : Fin D.R.rS) (b : Fin (D.R.rS + 1)) :
    ((Qi * (H⁻¹ * M * H) * Q) *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u')) b) (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) =
      ((Qi * M * Q) *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u')) b) (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) := by
  have hQQi := hT.2.1
  have hH := hT.2.2.1
  set f := Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u')) b with hf

  have hHf : H *ᵥ (Q *ᵥ f) = Q *ᵥ f := by
    have := fam_eq v hT u' hl b
    have e : Q *ᵥ f = lam ^ (D.R.rS - b.val) • Formalism.L2.SG.RealObj.frm X u' 1 v b := by
      rw [this, smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hl), one_smul]
    rw [e, Matrix.mulVec_smul]
    congr 1
    unfold Formalism.L2.SG.RealObj.frm Formalism.L2.SG.RealObj.famSc Formalism.L2.SG.RealObj.fam
    simp only [Complex.ofReal_one, one_pow, inv_one, one_smul]
    refine Fin.lastCases ?_ (fun c => ?_) b
    · rw [Fin.snoc_last]; exact hz
    · rw [Fin.snoc_castSucc]; exact he c

  have hread : ∀ x : Fin X.B.I.n → ℂ, (Qi *ᵥ x) (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) =
      (lam ^ (D.R.rS - a.val))⁻¹ * hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) x := by
    intro x
    have hfR : rv X.B.I v (X.fR a) = star (lam ^ (D.R.rS - a.val)) • (Q *ᵥ Pi.single (Formalism.QuantumDeterminants.esI D.R.k D.R.rS a) 1) := by
      rw [(hT.2.2.2 a a rfl).2, smul_smul, mul_inv_cancel₀, one_smul]
      exact star_ne_zero.2 (pow_ne_zero _ hl)
    have hx : x = Q *ᵥ (Qi *ᵥ x) := by rw [Matrix.mulVec_mulVec, hQQi, Matrix.one_mulVec]
    rw [hfR]
    conv_rhs => rw [hx]
    unfold hJ
    rw [star_smul, smul_dotProduct, ← Formalism.L2.SG.Pf.LTL.star_dot_conjT, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hH,
      Pi.star_single, star_one, single_dotProduct, one_mul, Formalism.L2.SG.RealFrameCoordinates.hpk_esI, smul_eq_mul, star_star,
      ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hl), one_mul]
  have hisom : ∀ x y : Fin X.B.I.n → ℂ, hJ (X.B.I.ε v) (H *ᵥ x) (H *ᵥ y) = hJ (X.B.I.ε v) x y := by
    intro x y
    unfold hJ
    rw [← Formalism.L2.SG.HermitianMatrixIdentities.star_dot_conjT' H x (Formalism.REAL.Jm (X.B.I.ε v) *ᵥ (H *ᵥ y)), Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, hHU]
  have hinvJ : ∀ x : Fin X.B.I.n → ℂ, hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (H⁻¹ *ᵥ x) =
      hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) x := by
    intro x
    have hx : H *ᵥ (H⁻¹ *ᵥ x) = x := by rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hHu, Matrix.one_mulVec]
    rw [← hisom, hfa a, hx]
  have e1 : (Qi * (H⁻¹ * M * H) * Q) *ᵥ f = Qi *ᵥ (H⁻¹ *ᵥ (M *ᵥ (Q *ᵥ f))) := by
    simp only [← Matrix.mulVec_mulVec, hHf]
  have e2 : (Qi * M * Q) *ᵥ f = Qi *ᵥ (M *ᵥ (Q *ᵥ f)) := by
    simp only [← Matrix.mulVec_mulVec]
  rw [e1, e2, hread, hread, hinvJ]

end Formalism.L2.SG.StandardCoordinates

end
end
