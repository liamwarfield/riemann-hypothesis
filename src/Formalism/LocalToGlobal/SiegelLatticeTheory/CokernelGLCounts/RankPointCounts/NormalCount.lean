module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqVanish
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NmlIntHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXCC
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXLeaves
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SgnConjIntUp
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MemOfBcPMem
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DensFrame
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.IsometryFixFlagAnisotropicVectorOfFixFrame

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormalCount
namespace Formalism.L2.SG.NGCut.NormalCount

theorem NormCountG_holds : Formalism.L2.SG.NGCut.NormalInvariants.NormCountG := by
  intro E _ _ _ J m hJ hm S hS
  exact Formalism.L2.SG.NGCut.TorsionTotientBound.card_mul_conj_eq_le_of_fractionalIdeal E J m hJ hm S hS

theorem NormCount_holds : Formalism.L2.SG.NGCut.NormalInvariants.NormCount :=
  Formalism.L2.SG.NGCut.NormalInvariants.normCount_of NormCountG_holds

end Formalism.L2.SG.NGCut.NormalCount
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataPos
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.MassDataPos

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets
  Formalism.L2.SG.MassDataConc MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem glkC_pos (k g : ℕ) (hg : g.Prime) : 0 < glkC k g := by
  haveI : NeZero g := ⟨hg.ne_zero⟩
  unfold glkC
  exact Nat.card_pos

theorem ukC_pos (k g : ℕ) (hg : g.Prime) : 0 < ukC k g := by
  haveI : NeZero g := ⟨hg.ne_zero⟩
  unfold ukC
  exact Nat.card_pos

theorem ggC_pos (r k g : ℕ) (hg : g.Prime) : 0 < ggC r k g := by
  haveI : NeZero g := ⟨hg.ne_zero⟩
  unfold ggC
  exact Nat.card_pos

theorem nnC_pos (r k g : ℕ) (hg : g.Prime) : 0 < nnC r k g := by
  haveI : NeZero g := ⟨hg.ne_zero⟩
  unfold nnC
  rw [Nat.card_pos_iff]
  refine ⟨⟨⟨1, ?_⟩⟩, inferInstance⟩
  unfold Formalism.FourierDecayAlt.S3.IsN
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (simp only [Formalism.DoubleCosetMeasures.IsUpUni, Formalism.FourierDecayAlt.S3.b11, Formalism.FourierDecayAlt.S3.b33, Formalism.FourierDecayAlt.S3.b22, Formalism.FourierDecayAlt.S3.b21, Formalism.FourierDecayAlt.S3.b31, Formalism.FourierDecayAlt.S3.b32]
       exact ⟨fun i j hij => by simp [Matrix.one_apply, (show j < i from hij).ne'], fun a => by simp [Matrix.one_apply]⟩)
    | (simp [Formalism.FourierDecayAlt.S3.b11, Formalism.FourierDecayAlt.S3.b33, Formalism.FourierDecayAlt.S3.b22, Formalism.FourierDecayAlt.S3.b21, Formalism.FourierDecayAlt.S3.b31, Formalism.FourierDecayAlt.S3.b32, Matrix.one_apply]; done)
    | (ext i j; simp [Formalism.FourierDecayAlt.S3.b11, Formalism.FourierDecayAlt.S3.b33, Formalism.FourierDecayAlt.S3.b22, Formalism.FourierDecayAlt.S3.b21, Formalism.FourierDecayAlt.S3.b31, Formalism.FourierDecayAlt.S3.b32, Matrix.one_apply]; done)

section Main

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

abbrev bk : Formalism.FourierDecayAlt.S3.MassData (TypX X) := bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq

def MassDataPosC : Prop := (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).Pos

def LocHaarPosC : Prop :=
  (∀ p, 0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μKp p ∧
    0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μKnatp p ∧
    0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μKppp p ∧
    0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μSp p ∧
    0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μSp' p ∧
    0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μSppp p ∧
    0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μSppp' p) ∧
  0 < (X.measG.μGf (Formalism.L2.SG.Sub.Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)))).toReal ∧
  0 < ((X.measW u).μSf (Subtype.val ⁻¹' (Formalism.L2.SG.Sub.Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :
      Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.B.I.F) X.B.I.cm.sig X.B.I.J)))).toReal ∧
  0 < ((X.measW u').μSf (Subtype.val ⁻¹' (Formalism.L2.SG.Sub.Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :
      Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.B.I.F) X.B.I.cm.sig X.B.I.J)))).toReal ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μH ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μH' ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μHpp ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μHpp' ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μN ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μN'

def CovolPosC : Prop :=
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volG ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volHa ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volHa' ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volNa ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volNa' ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volB

def QuotVolPosC : Prop :=
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volH ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volH' ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volN ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volN'

def RecPosC : Prop :=
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).deg ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).dimπ ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).dimπ' ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).ρ0 ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).ρ0' ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).d ∧
  0 < (bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).d'

theorem gOf_prime (p : TypX X) : (gOf p).Prime := by
  unfold gOf
  split_ifs
  · exact D.host.g_prime 0
  · exact D.host.g_prime 1

theorem massDataPosC_of (hL : LocHaarPosC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq)
    (hCv : CovolPosC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq)
    (hQv : QuotVolPosC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq)
    (hR : RecPosC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq)
    (hP : Formalism.L2.SG.LocVol.ProdConv X u u' ψ) (hCoo : 0 < Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1)
    (hκ : 0 < Formalism.L2.SG.MassDataConc.kapN D) (hsd : 0 ≤ sd) (hC : 0 ≤ C) (hTh : 0 < Th) :
    MassDataPosC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq := by
  obtain ⟨hv, -, -, -, hUo, -, hZZ, hPP, -, hal, -⟩ := hP
  obtain ⟨hloc, hGf, hSf, hSf', hH, hH', hHpp, hHpp', hN, hN'⟩ := hL
  obtain ⟨hG, hHa, hHa', hNa, hNa', hB⟩ := hCv
  obtain ⟨hvH, hvH', hvN, hvN'⟩ := hQv
  obtain ⟨hdeg, hdp, hdp', hr0, hr0', hd, hd'⟩ := hR
  set B := bk X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq with hBdef
  have hMp : ∀ p, 0 < B.Mp p := fun p => (hv p.1).1 p.2
  have hU00p : ∀ p, 0 < B.localVolumeAtPlace p := fun p => (hv p.1).2.1
  have hKo : 0 < B.μKo := div_pos hGf (Finset.prod_pos fun p _ => (hloc p).1)
  have hSo : 0 < B.μSo := div_pos hSf (Finset.prod_pos fun p _ => (hloc p).2.2.2.1)
  have hSo' : 0 < B.μSo' := div_pos hSf' (Finset.prod_pos fun p _ => (hloc p).2.2.2.2.1)
  have hU00o : 0 < B.localVolumeArchimedean := hUo
  have hMo : 0 < B.Mo := div_pos (mul_pos hU00o (pow_pos hKo 2)) (mul_pos hSo hSo')
  have hZ : 0 < B.volZZ := hZZ
  have hPPp : 0 < B.volPP := by
    show 0 < ∏ l : Fin (D.R.rS + 1), ∏' v : Formalism.L2.SG.LocVol.PlX X, Formalism.L2.SG.LocVol.PPX X u u' ψ l v
    exact Finset.prod_pos fun l _ => (hPP l).2
  have hAl : 0 < B.al := mul_pos (Finset.prod_pos fun p _ => (hv p.1).2.2.2.2) hal
  have hCo : 0 < B.Coo := mul_pos hκ hCoo
  have hMM : 0 < B.MM := mul_pos hMo (Finset.prod_pos fun p _ => hMp p)
  have hμK : 0 < B.μK := mul_pos hKo (Finset.prod_pos fun p _ => (hloc p).1)
  have hAA : 0 < B.AA := div_pos (mul_pos (mul_pos hB hCo) (div_pos hMM hZ)) hμK
  have hn0c : 0 < B.n0c := div_pos hAA hr0
  have hgp : ∀ p, 0 < B.g p := fun p => by
    show (0 : ℝ) < ((gOf p : ℕ) : ℝ)
    exact_mod_cast (gOf_prime X p).pos
  have hglk : ∀ p, 0 < B.glk p := fun p => by
    show (0 : ℝ) < ((glkC D.R.k (gOf p) : ℕ) : ℝ)
    exact_mod_cast glkC_pos _ _ (gOf_prime X p)
  have huk : ∀ p, 0 < B.uk p := fun p => by
    show (0 : ℝ) < ((ukC D.R.k (gOf p) : ℕ) : ℝ)
    exact_mod_cast ukC_pos _ _ (gOf_prime X p)
  have hnn : ∀ p, 0 < B.nn p := fun p => by
    show (0 : ℝ) < ((nnC D.R.rS D.R.k (gOf p) : ℕ) : ℝ)
    exact_mod_cast nnC_pos _ _ _ (gOf_prime X p)
  have hgg : ∀ p, 0 < B.gg p := fun p => by
    show (0 : ℝ) < ((ggC D.R.rS D.R.k (gOf p) : ℕ) : ℝ)
    exact_mod_cast ggC_pos _ _ _ (gOf_prime X p)
  have hδ : 0 ≤ B.δ := by
    show 0 ≤ C * ((D.R.rS : ℝ) + 1) * (C / Th) ^ (Fintype.card (NumberField.InfinitePlace X.B.I.F))
    exact mul_nonneg (mul_nonneg hC (by positivity)) (pow_nonneg (div_nonneg hC hTh.le) _)
  unfold MassDataPosC Formalism.FourierDecayAlt.S3.MassData.Pos
  exact ⟨fun p => ⟨hgp p, hglk p, huk p, hnn p, hgg p, (hloc p).1, (hloc p).2.1, (hloc p).2.2.1, (hloc p).2.2.2.1,
      (hloc p).2.2.2.2.1, (hloc p).2.2.2.2.2.1, (hloc p).2.2.2.2.2.2, hMp p, hU00p p⟩,
    hKo, hSo, hSo', hMo, hU00o, hH, hH', hHpp, hHpp', hN, hN', hZ, hPPp, hAl, hG, hHa, hHa', hNa, hNa', hB, hvH, hvH',
    hvN, hvN', hCo, hdeg, hdp, hdp', hr0, hr0', hd, hd', hn0c, hsd, hδ⟩

end Main

theorem cooOf_pos {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) : 0 < Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1 := by
  have h := Formalism.L2.SG.RealObj.InfCut.ProductExactness.haar_disintegration_real_holds D X u u' 1 one_pos
  have h' : ∃ C, 0 < C ∧ Formalism.L2.SG.RealObj.Disint X u u' 1 C := h
  unfold Formalism.L2.SG.RealObj.DisintegrationConstant
  rw [dite_eq_left h']
  exact h'.choose_spec.1

theorem quotVolPosC_of {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (Y : Formalism.L2.SG.Full.Full X)
    (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
    {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
    {F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
    (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (hK2 : X.LevelSubgroupNormalized) (hV : 0 < X.volK2) :
    QuotVolPosC X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq := by
  obtain ⟨hN, hH⟩ := Formalism.L2.SG.Closed.VolPosC_holds D X Y u hK2
  obtain ⟨hN', hH'⟩ := Formalism.L2.SG.Closed.VolPosC_holds D X Y u' hK2
  refine ⟨hH, hH', ?_, ?_⟩
  · show 0 < ((X.muN u) (Y.FN u)).toReal
    exact pos_of_mul_pos_right hN hV.le
  · show 0 < ((X.muN u') (Y.FN u')).toReal
    exact pos_of_mul_pos_right hN' hV.le

end Formalism.L2.SG.Pf.MassDataPos
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CovolumeSpans
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full

namespace Formalism.L2.SG.KappaOffDiagonal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem vector_eq_zero_of_orbital_zero {D : D7} {X : HidaSetting D} (Y : Full X) {u : D.what₂.Word} (t : GTu Y u)
    (h : OOt t = 0) : (Y.tO u u).vec t = 0 := by
  unfold Full.tO tOf
  dsimp only
  unfold vec ampN
  rw [h]
  simp only [map_zero, smul_zero, ite_self]
  first
    | rfl
    | simp

theorem irrVec_nohyp {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word) (t : GTu Y u) (ht : ¬ t.relevant) :
    (Y.tO u u).vec t = 0 :=
  vector_eq_zero_of_orbital_zero Y t
    (Vanish.ooVanish_of Formalism.L2.SG.Closed.AvgCore_holds Formalism.L2.SG.Pf.ginfUnimod_holds Formalism.L2.SG.Pf.nLamNinf_holds
      Formalism.L2.SG.Closed.ChiTrivialC_holds Formalism.L2.SG.Pf.psiInfChar_holds Formalism.L2.SG.Pf.rClosedC_holds
      Formalism.L2.SG.Pf.roDiscreteC_holds Formalism.L2.SG.TermOp.Vanish.rational_cocompact_holds Formalism.L2.SG.NonRelPf.nonRelCharC_holds Y t ht)

theorem IrrVecC_holds : IrrVecC := by
  intro D X Y u _ _ t _ ht
  exact irrVec_nohyp Y u t ht

end Formalism.L2.SG.KappaOffDiagonal
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqNml
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps
  Formalism.L2.SG.NGCut.NormalVectorPairings

set_option linter.dupNamespace false

namespace Formalism.L2.SG.Pf.MainEqNml

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word)

def OccTG (c : Set (TauC Y u u)) (γ : PN.Pts D.host.E D.R.rS) (t : TauC Y u u) : Prop :=
  t ∈ (Y.tO u u).genSet ∧ (Y.tO u u).vec t ≠ 0 ∧ clsG Y u t = c ∧ ptPN t = γ

theorem occ_iffG (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ)
    (c : Set (TauC Y u u)) (γ : PN.Pts D.host.E D.R.rS) (ν : NuC D) :
    PN.Occ (genT (Y.tO u u)) (NOfG Y u νL νB ng) c γ ν ↔ ∃ t, OccTG Y u c γ t ∧ nmlOf Y u u t = ν := by
  constructor
  · rintro ⟨t, h1, h2, h3, h4, h5⟩
    have e : t ∈ (Y.tO u u).genSet := by
      simp only [genT, Formalism.FourierDecayAlt.PB.Terms.ngSet, Formalism.FourierDecayAlt.PB.Terms.genSet, Set.mem_setOf_eq, not_not] at h1 ⊢
      exact h1
    exact ⟨t, ⟨e, h2, h3, h4⟩, h5⟩
  · rintro ⟨t, ⟨h1, h2, h3, h4⟩, h5⟩
    have e : t ∈ (genT (Y.tO u u)).ngSet := by
      simp only [genT, Formalism.FourierDecayAlt.PB.Terms.ngSet, Formalism.FourierDecayAlt.PB.Terms.genSet, Set.mem_setOf_eq, not_not] at h1 ⊢
      exact h1
    exact ⟨t, e, h2, h3, h4, h5⟩

variable {Y u}

theorem relC_of_occG (hE : ScalEquivOn (Y.tO u u)) {c : Set (TauC Y u u)} {γ : PN.Pts D.host.E D.R.rS}
    {t0 t : TauC Y u u} (h0 : OccTG Y u c γ t0) (h : OccTG Y u c γ t) : RelC Y u u t0 t := by
  unfold Formalism.L2.SG.Pf.MainEqSteps.ScalEquivOn at hE
  obtain ⟨h01, h02, h03, h04⟩ := h0
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hmem : t ∈ clsG Y u t := ⟨h1, rfl, (hE.1 t h1).1, (hE.1 t h1).2⟩
  rw [h3, ← h03] at hmem
  exact ⟨hmem.2.1, hmem.2.2.1⟩

end Formalism.L2.SG.Pf.MainEqNml

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.MainEqNml

theorem nmlInvG_of (hL : NmlLine) (hI : NmlInt) (hS : NmlSep) : Formalism.L2.SG.NGCut.NormalInvariants.Gen.NmlInvG := by
  intro Cg cb Cw cT CT C0
  obtain ⟨a1, b1, H1⟩ := hL Cg cb Cw cT CT C0
  obtain ⟨a2, b2, H2⟩ := hI Cg cb Cw cT CT C0
  obtain ⟨a3, b3, H3⟩ := hS Cg cb Cw cT CT C0
  refine ⟨max a1 (max a2 a3), max b1 (max b2 b3), fun C' Cl hC hCl D large₂ X Y u hctx νL νB ng c γ hocc hNG => ?_⟩
  have hC1 : a1 ≤ C' := le_trans (le_max_left _ _) hC
  have hC2 : a2 ≤ C' := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC
  have hC3 : a3 ≤ C' := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC
  have hl1 : b1 ≤ Cl := le_trans (le_max_left _ _) hCl
  have hl2 : b2 ≤ Cl := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCl
  have hl3 : b3 ≤ Cl := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCl
  obtain ⟨ν0, hν0⟩ := hocc
  obtain ⟨t0, ht0, -⟩ := (occ_iffG Y u νL νB ng c γ ν0).1 hν0
  have hE : ScalEquivOn (Y.tO u u) := stepClassG_holds D X Y u (g_ge_three hctx) hctx.2.2
  have hG0 : Gt t0 ≠ 0 := ht0.1.1
  obtain ⟨J, J', hJ, hJ', hmem, hb, hb'⟩ := H2 C' Cl hC2 hl2 D large₂ X Y u u hctx γ hNG t0 hG0 ht0.2.2.2
  set pick : NuC D → TauC Y u u := fun ν =>
    if h : ∃ t, OccTG Y u c γ t ∧ nmlOf Y u u t = ν then h.choose else t0 with hpick
  have hpick_spec : ∀ ν, PN.Occ (genT (Y.tO u u)) (NOfG Y u νL νB ng) c γ ν →
      OccTG Y u c γ (pick ν) ∧ nmlOf Y u u (pick ν) = ν := by
    intro ν hν
    have h := (occ_iffG Y u νL νB ng c γ ν).1 hν
    simp only [hpick, dif_pos h]
    exact h.choose_spec
  refine ⟨J, J', 1, 1, fun ν => (coefA Y u u t0 (pick ν), coefA' Y u u t0 (pick ν)), hJ, hJ', one_ne_zero,
    one_ne_zero, fun ν hν => ?_, fun ν₁ ν₂ h₁ h₂ hκ => ?_, ?_, ?_⟩
  · obtain ⟨hp, -⟩ := hpick_spec ν hν
    obtain ⟨m1, m2⟩ := hmem _ hp.1.1 hp.2.2.2 (relC_of_occG hE ht0 hp)
    obtain ⟨n1, n2⟩ := H1 C' Cl hC1 hl1 D large₂ X Y u u hctx γ hNG t0 _ hG0 hp.1.1 ht0.2.2.2 hp.2.2.2
      (relC_of_occG hE ht0 hp)
    exact ⟨m1, n1, m2, n2⟩
  · obtain ⟨hp1, he1⟩ := hpick_spec ν₁ h₁
    obtain ⟨hp2, he2⟩ := hpick_spec ν₂ h₂
    have hk1 := congrArg Prod.fst hκ
    have hk2 := congrArg Prod.snd hκ
    simp only at hk1 hk2
    rw [← he1, ← he2]
    exact H3 C' Cl hC3 hl3 D large₂ X Y u u hctx γ hNG t0 _ _ hG0 hp1.1.1 hp2.1.1 ht0.2.2.2 hp1.2.2.2 hp2.2.2.2
      (relC_of_occG hE ht0 hp1) (relC_of_occG hE ht0 hp2) hk1 hk2
  · rw [map_one]
    simpa using hb
  · rw [map_one]
    simpa using hb'

end Formalism.L2.SG.Pf
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqFam
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc
  Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqLoc

namespace Formalism.L2.SG.Pf.MainEqFam

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ampG {Cl Nu : Type} (L : PN.LocalNG Cl Nu) (d : ∀ p, L.D p) : ℂ := ∏ p, L.aZ p (d p)

variable {D : D7}

theorem localLeG_of_fam {Z : LocDat D} {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁) {Cl Nu : Type}
    (N : PN.NGData τ D.host.E D.R.rS Cl Nu) (C1 C0n : ℕ) (AAre : ℝ) (hk : 2 * D.R.rS + 5 ≤ D.R.k)
    (hQ : Formalism.MainNotions.NonGenericAndKTwoTheorems.NonGenericLocalBound D.R.k D.R.rS (C1 : ℝ))
    (h : ∀ γ, PN.IsPt X N γ → ∀ S : Finset (Cl × Nu), ∃ Fm : LocFam Z Cl Nu,
      FamOKS N γ S C0n AAre (fun L => ampG L) Fm) :
    LocalInputLeG X N C1 C0n AAre := by
  intro γ hγ S
  obtain ⟨Fm, hR, hex, hOm, hD, hn, hV0, hrw, hM, hU, ha, hH, hpos, hle⟩ := h γ hγ S
  have hrank : ∀ p : PlF D, Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
    intro p
    rw [finrank_Vp]
    have h1 := D.R.r_eq
    have h2 : 2 * D.R.rS + 2 = D.R.m := by
      have hm2 := D.R.two_le_m
      obtain ⟨j, hj⟩ := D.R.m_even
      simp only [Formalism.BasicNotions.Ranks.rS]; omega
    omega
  have hNG : ∀ p ∈ Fm.P, LocNG.NGAt D.R.k (Fm.FP p) (C1 : ℝ) := fun p hp =>
    hQ (D.s.atP p).Fp (D.s.atP p).Ep (Z.M p) (Z.agree p).1 (Vp D p) (locH Z p) (hrank p) (Fm.FP p) (hR p hp)
  have hq2 : ∀ p ∈ Fm.P, 2 ≤ LocNG.qF (D.s.atP p).Fp := fun p hp => Formalism.MainNotions.KappaEndpoints.two_le_residue_card (Z.agree p).1
  have hqH : ∀ p ∈ Fm.P, ¬ (Fm.FP p).PrimeTo → (LocNG.qF (D.s.atP p).Fp : ℝ) ≤ (Fm.FP p).Hp := fun p hp hpr =>
    Formalism.L2.SG.Pf.residue_le_height_nonprime (Z.agree p).1 (hR p hp) (hex p hp) hpr
  have hH1 : ∀ p ∈ Fm.P, 1 ≤ (Fm.FP p).Hp := by
    intro p hp
    by_cases hpr : (Fm.FP p).PrimeTo
    · exact le_of_eq ((hNG p hp (Fm.R p) (Fm.d0 p)).2.2.2 hpr).1.symm
    · have h2 : (2 : ℝ) ≤ (LocNG.qF (D.s.atP p).Fp : ℝ) := by exact_mod_cast hq2 p hp
      linarith [hqH p hp hpr]
  have hHp : ∀ p ∈ Fm.P, 0 ≤ (Fm.FP p).Hp := fun p hp => le_trans zero_le_one (hH1 p hp)
  have hB : Fm.toL.Basic := by
    refine ⟨fun p d => ?_, fun p => hH1 p.1 p.2, fun p => hq2 p.1 p.2, fun p hp => hqH p.1 p.2 ((hOm p).1 hp),
      fun p => ENNReal.toReal_nonneg, hV0, hrw⟩
    show 0 ≤ LocNG.Datum.wt (Fm.d0 p.1) d.1
    unfold LocNG.Datum.wt LocNG.volRel
    positivity
  exact ⟨Fm.toL, hB, (ngAt_toL Fm C1 hk hNG hD hn hHp).2, hM, hU, ha, hH, hpos, hle⟩

def StepFamG : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C0n : ℕ, ∃ CSt : ℝ, 0 ≤ CSt ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ →
      ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
        (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
        (vR : Formalism.L2.SG.TermDef.Term D u u F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u F0 what₂)
        (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (Irat Ire : ℝ),
        MassDataAdmissible X Y u u (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire →
      ∀ ν, Pinned X u u ν →
      ∃ s : X.B.I.Ginf → NNReal,
        (∀ γ, Formalism.L2.SG.RealObj.RegX X u u γ → s γ = 1) ∧ (∀ γ, 0 < s γ) ∧
        (∀ γ, (s γ : ℝ) ^ 2 ≤ large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f)) ∧
        ∀ γ, PN.IsPt (genT (Y.tO u u)) (NOfG Y u (sc s ν) ν (fun _ => 0)) γ →
          ∀ S : Finset (Set (TauC Y u u) × NuC D), ∃ Fm : LocFam (zOf Y) (Set (TauC Y u u)) (NuC D),
            FamOKS (NOfG Y u (sc s ν) ν (fun _ => 0)) γ S C0n
              (PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq).AA)
              (fun L => ampG L) Fm

end Formalism.L2.SG.Pf.MainEqFam

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.MainEqFam

theorem stepLocPinnedG_of_fam (hQ5 : ∀ D : D7, Formalism.MainNotions.NonGenericAndKTwoTheorems.Conclusion1 D 39) (hF : StepFamG) : StepLocPinnedG := by
  intro Cg cb Cw cT CT C0
  obtain ⟨C0n, CSt, hCSt, a₀, b₀, h2⟩ := hF Cg cb Cw cT CT C0
  refine ⟨39, C0n, CSt, hCSt, a₀, b₀, fun C' Cl e1 e2 D large₂ X Y u hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq
    Irat Ire hBk ν hν => ?_⟩
  obtain ⟨s, hs1, hs0, hsb, hL⟩ := h2 C' Cl e1 e2 D large₂ X Y u hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat
    Ire hBk ν hν
  have hk4 : 4 * D.R.rS + 7 ≤ D.R.k := by
    obtain ⟨⟨hH, _, _⟩, _, _⟩ := hc
    unfold Formalism.MainNotions.S.StandingHypotheses at hH
    dsimp only at hH
    obtain ⟨-, -, h3, h4, -⟩ := hH
    have hm2 := D.R.two_le_m
    obtain ⟨j, hj⟩ := D.R.m_even
    have hmr : 2 * D.R.rS + 2 = D.R.m := by simp only [Formalism.BasicNotions.Ranks.rS]; omega
    have : 2 * D.R.m + 3 ≤ D.R.m ^ 4 := by nlinarith [Nat.pow_le_pow_left hm2 3]
    omega
  have hQ : Formalism.MainNotions.NonGenericAndKTwoTheorems.NonGenericLocalBound D.R.k D.R.rS ((39 : ℕ) : ℝ) := by
    have := hQ5 D hk4
    exact_mod_cast this
  exact ⟨s, hs1, hs0, hsb, localLeG_of_fam _ _ 39 C0n _ (by omega) hQ hL⟩

end Formalism.L2.SG.Pf
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NmlInvHolds
namespace Formalism.L2.SG.NGCut.NormalVectorPairings

theorem NmlInv_holds : Formalism.L2.SG.NGCut.NormalInvariants.NmlInv :=
  nmlInv_of NmlLine_holds Formalism.L2.SG.NGCut.NormalIntegrality.NmlInt_holds NmlSep_holds

end Formalism.L2.SG.NGCut.NormalVectorPairings
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FormRel
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic

namespace Formalism.L2.SG.Pf.FormRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def FormRelC : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ ν, Pinned X u u' ν → ∀ t ∈ (Y.tO u u').nzSet, (Y.tO u u').vec t ≠ 0 →
        (∃ w : Point D.host.E (D.R.rS + 1), toPts w = ptPN t ∧ ∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g) ∧
        ∀ w : Point D.host.E (D.R.rS + 1), toPts w = ptPN t → (∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g) →
          ∃ (c : ℂ) (A : X.Vpi u →L[ℂ] X.Vpi u) (B : X.Vpi u' →L[ℂ] X.Vpi u'),
            OOt t = c • A.comp ((haveI := FiniteDimensional.complete ℂ (X.Vpi u)
              OO (ν (Formalism.L2.SG.RealObj.gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u')
                (Formalism.L2.SG.RealObj.gamW X u u' w)).comp B)

end Formalism.L2.SG.Pf.FormRel

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.FormRel

theorem formNGC_of_rel (h : FormRelC) : Formalism.L2.SG.NGVanish.FormNGC := by
  intro Cg cb Cw cT CT C0
  obtain ⟨C'₀, Cl₀, hC⟩ := h Cg cb Cw cT CT C0
  refine ⟨C'₀, Cl₀, fun C' Cl h1 h2 D large₂ X Y u u' hx ν hν t ht hv => ?_⟩
  have hnz : t ∈ (Y.tO u u').nzSet := by
    exact ht.1
  exact hC C' Cl h1 h2 D large₂ X Y u u' hx ν hν t hnz hv

theorem formGC_of_rel (h : FormRelC) : Formalism.L2.SG.Pf.MainEqVanish.FormGC := by
  intro Cg cb Cw cT CT C0
  obtain ⟨C'₀, Cl₀, hC⟩ := h Cg cb Cw cT CT C0
  refine ⟨C'₀, Cl₀, fun C' Cl h1 h2 D large₂ X Y u hx ν hν t ht hv => ?_⟩
  have hnz : t ∈ (Y.tO u u).nzSet := by
    exact ht.1
  exact hC C' Cl h1 h2 D large₂ X Y u u hx ν hν t hnz hv

end Formalism.L2.SG.Pf
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NofibOf
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NOinfClosedUnderMulInv
namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting

theorem nOinf_closed_under_mul_inv {D : D7} (X : HidaSetting D) (u : D.what₂.Word) :
    Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u ⊆ X.NinfU u ∧
    (∀ δ ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u, ∀ δ' ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u,
      δ * δ' ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u) ∧
    (∀ δ ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u, δ⁻¹ ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u) := by
  have hK := Formalism.L2.SG.Closed.level_subgroup_is_group X
  have hc := Formalism.L2.SG.Pf.NOsub_coe X u hK
  refine ⟨fun s hs => Formalism.L2.SG.Pf.no_sub_ninf X u hs, fun δ hδ δ' hδ' => ?_, fun δ hδ => ?_⟩
  · rw [← hc] at hδ hδ' ⊢
    exact (Formalism.L2.SG.Pf.NOsub X u hK).mul_mem hδ hδ'
  · rw [← hc] at hδ ⊢
    exact (Formalism.L2.SG.Pf.NOsub X u hK).inv_mem hδ

end Formalism.L2.SG.Pf.NcReal.JX
end

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting NumberField

def NOfibLat : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word),
    ∃ τ : ∀ p : CBlk D.R.rS, (∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q) → CSpc (InfinitePlace X.B.I.F) D.R.k p,
      (∀ p (x x' : ∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q), (∀ q, cHgt q < cHgt p → x q = x' q) → τ p x = τ p x') ∧
      ∀ x : ∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q,
        x ∈ blk X u '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u ↔ ∀ p, x p - τ p x ∈ cLat X u p

theorem nofib_of (hL : NOfibLat) : NOfib := by
  intro D X u
  obtain ⟨h1, h2, h3⟩ := nOinf_closed_under_mul_inv X u
  exact ⟨h1, h2, h3, hL X u⟩

end Formalism.L2.SG.Pf.NcReal.JX
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MemDdSPow
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DdPowConj
noncomputable section

open scoped Classical Matrix
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc

namespace Formalism.L2.SG.Pf.FibD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem ddPow_conj (Zd : LocDat D) {k : ℕ} (hk : k ≤ D.R.rS) {y : D.host.E} (h : y ∈ Formalism.L2.SG.Pf.StabIntSh.ddPow D k) :
    D.conjF y ∈ Formalism.L2.SG.Pf.StabIntSh.ddPow D k := by
  have hne := (Formalism.L2.SG.Pf.StabIntSh.shapeNZ (D := D)).1 k
  exact (Formalism.L2.SG.Pf.StabIntSh.locGlob _ hne _).1 fun p =>
    Formalism.L2.SG.Pf.StabIntSh.locMem_conj Zd.δ Zd.M Zd.agree p hk
      ((Formalism.L2.SG.Pf.StabIntSh.locGlob _ hne _).2 h p)

theorem mem_aaF {c b : Fin (D.R.rS + 1)} (hcb : c < b) {x y : D.host.E} (hx : x ∈ FibQ.aaF D b)
    (hy : y ∈ Formalism.L2.SG.Pf.StabIntSh.ddPow D (b.val - c.val)) : x * y ∈ FibQ.aaF D c := by
  have h := FractionalIdeal.mul_mem_mul hx hy
  unfold FibQ.aaF Formalism.L2.SG.Pf.StabIntSh.ddPow at *
  rw [← zpow_add₀ (PI.NRCW.ddS_ne_zero D)] at h
  have e : -((D.R.rS : ℤ) - ((b : ℕ) : ℤ)) + -(((b.val - c.val : ℕ)) : ℤ) = -((D.R.rS : ℤ) - ((c : ℕ) : ℤ)) := by
    have : c.val ≤ b.val := le_of_lt hcb
    push_cast [this]
    ring
  rwa [e] at h

theorem sg_entry (B : Formalism.L2.SG.PairVal.MatR D) (c b : Fin (D.R.rS + 1)) :
    (Formalism.L2.SG.Pf.AtPt.Sg D.host.E D.R.rS * B * Formalism.L2.SG.Pf.AtPt.Sg D.host.E D.R.rS) c b =
      Formalism.L2.SG.Pf.StabIntSh.bt D B c b := by
  simp [Formalism.L2.SG.Pf.AtPt.Sg, Formalism.L2.SG.Pf.StabIntSh.bt, Matrix.mul_diagonal, Matrix.diagonal_mul]

end Formalism.L2.SG.Pf.FibD
end
end

noncomputable section

open scoped Classical Matrix
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc

namespace Formalism.L2.SG.Pf.FibD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem mem_ddS_pow (t : 𝓞 D.host.F) (ht : t ∈ differentIdeal ℤ (𝓞 D.host.F)) (k : ℕ) :
    (((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t) ^ k : 𝓞 D.host.E) : D.host.E) ∈ ddS D ^ k := by
  have h1 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t ∈
      Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)) :=
    Ideal.mem_map_of_mem _ ht
  have h2 : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t : 𝓞 D.host.E) : D.host.E) ∈ ddS D :=
    FractionalIdeal.mem_coeIdeal_of_mem _ h1
  have h3 := Submodule.pow_mem_pow (ddS D : Submodule (𝓞 D.host.E) D.host.E) h2 k
  rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_pow]
  push_cast
  exact h3

theorem dict_holds (Zd : LocDat D) : Formalism.L2.SG.Pf.TupGlob.Dict Zd := by
  intro A B hA hB hloc
  have hAu : IsLoUni A := fun i j => ⟨hA.2 i j, fun h => h ▸ hA.1 i⟩
  have hBu : IsUpUni B := Formalism.L2.SG.Pf.TupGlob.isUpUni_of hB
  have hsh : ∀ p, Formalism.L2.SG.Pf.StabIntSh.LocEntryShape D p A B := fun p =>
    (Formalism.L2.SG.Pf.StabIntSh.loc_iff Formalism.L2.SG.Pf.StabIntSh.locShapeL Formalism.L2.SG.Pf.StabIntSh.locShapeG (p := p)
      Zd.agree hAu hBu).1
      ⟨by rw [lOf_eq]; exact (hloc p).1, by rw [ρOf_eq]; exact Formalism.L2.SG.Pf.FibQ.sgn_conj_intUp Zd p (hloc p).2⟩
  have hES := (Formalism.L2.SG.Pf.StabIntSh.glob_iff Formalism.L2.SG.Pf.StabIntSh.locGlob Formalism.L2.SG.Pf.StabIntSh.shapeNZ A B).1 hsh
  refine ⟨fun c b hcb x hx => ?_, fun c b hcb x hx => ?_, fun P hP c b => ?_⟩
  · rw [Matrix.conjTranspose_apply, PI.UnitaryGroupMassFormula.CntFormula.star_eq_conjF]
    exact mem_aaF hcb hx (ddPow_conj Zd (by have := b.isLt; omega) (hES b c hcb).1)
  · rw [sg_entry]
    exact mem_aaF hcb hx (hES b c hcb).2.1
  · rcases lt_trichotomy c b with h | h | h
    · have hq := (hES b c h).2.2
      unfold Formalism.L2.SG.Pf.StabIntSh.qdPow Formalism.L2.SG.Pf.StabIntSh.qq at hq
      rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.mem_singleton_mul] at hq
      obtain ⟨z, hz, hzy⟩ := hq
      obtain ⟨t, ht, htP⟩ := diff_avoid P hP
      have hk : b.val - c.val ≤ D.R.rS := by have := b.isLt; omega
      have hz' := ddPow_conj Zd hk hz
      have hprod := FractionalIdeal.mul_mem_mul (mem_ddS_pow t ht (b.val - c.val)) hz'
      unfold Formalism.L2.SG.Pf.StabIntSh.ddPow at hprod
      rw [← zpow_natCast, ← zpow_add₀ (PI.NRCW.ddS_ne_zero D), add_neg_cancel, zpow_zero] at hprod
      obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 hprod
      refine ⟨(algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t) ^ (b.val - c.val), fun hs => htP (P.isPrime.mem_of_pow_mem _ hs),
        o, ?_⟩
      rw [Matrix.conjTranspose_apply, PI.UnitaryGroupMassFormula.CntFormula.star_eq_conjF, sg_entry]
      have e1 : D.conjF (A b c) - Formalism.L2.SG.Pf.StabIntSh.bt D B c b =
          D.conjF (algebraMap (𝓞 D.host.E) D.host.E ((gS D : ℕ) : 𝓞 D.host.E) * z) := by
        have := congrArg D.conjF hzy
        simpa only [map_sub, Formalism.L2.SG.Pf.LocalDenominators.conjF_invol] using this
      rw [e1, map_mul, map_natCast, map_natCast, mul_left_comm, ← ho]
    · subst h
      refine ⟨1, fun h1 => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1), 0, ?_⟩
      rw [Matrix.conjTranspose_apply, sg_entry]
      simp [Formalism.L2.SG.Pf.StabIntSh.bt, hA.1 c, hB.1 c, ← pow_add, ← two_mul, pow_mul]
    · refine ⟨1, fun h1 => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1), 0, ?_⟩
      rw [Matrix.conjTranspose_apply, sg_entry]
      simp [Formalism.L2.SG.Pf.StabIntSh.bt, hA.2 b c h, hB.2 b c h]

end Formalism.L2.SG.Pf.FibD
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowLatOfMove
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FrameActOne
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdCut

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem frameAct_one {n : ℕ} (f : Fin n → (VS D).V) (b : Fin n) : frameAct f 1 b = f b := by
  simp [frameAct, Matrix.one_apply]

theorem sgnP_mem (p : PlF D) (b : Fin (D.R.rS + 1)) : TermLoc.sgnP D p b ∈ (D.s.atP p).O := by
  rw [(D.s.atP p).O_def]
  refine ⟨Polynomial.X ^ 2 - 1, by monicity!, ?_⟩
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_one]
  rw [pow_two, TermLoc.localSign_sq, sub_self]


set_option maxHeartbeats 1000000 in
theorem btAdm : BtAdm Zd u u' F0 what₂ := by
  intro hC γ Z F'₂ φ φ' Λ₂ hs
  obtain ⟨_, _, ⟨hlat, hloc⟩, _⟩ := hs
  refine ⟨fun a b h => Matrix.one_apply_ne h.ne', fun a => Matrix.one_apply_eq a, fun b => ?_⟩
  intro P hgP
  rw [frameAct_one]
  haveI := P.isPrime
  set x : (VS D).V := frame (liftF F'₂) b - frame (lf D F0) b with hx
  obtain ⟨p, hpdef⟩ : ∃ p : PlF D, p = Formalism.L2.SG.Pf.LocalDenominators.plOf P.asIdeal P.isMaximal := ⟨_, rfl⟩
  have hPp : P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal := by rw [hpdef]; rfl
  have hty : Loc.resChar p ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ) :=
    (Formalism.L2.SG.Pf.BBTie.bt_g_mem_iff p P hPp).1 hgP
  obtain ⟨sg, hsg⟩ := Option.isSome_iff_exists.1 ((D.s_split p).2 hty)
  have hag := (Zd.agree p).2.2.2.2.2
  obtain ⟨g', hMs⟩ : ∃ g', (Zd.M p).split = some g' := by
    cases hm : (Zd.M p).split with
    | none => rw [hm, hsg] at hag; exact hag.elim
    | some g' => exact ⟨g', rfl⟩
  have hadm := ((hloc p).1.1.2.2.2.2.2 g' hMs).2.2 b

  have hrow := hC.2.1.1 γ.lam γ.mem
  have hgP' : ∀ P' : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E),
      P'.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal → (gS D : 𝓞 D.host.E) ∈ P'.asIdeal :=
    fun P' hP' => (Formalism.L2.SG.Pf.BBTie.bt_g_mem_iff p P' hP').2 hty
  obtain ⟨-, w, hw, hw1⟩ := Formalism.L2.SG.Pf.BBTie.bt_typed_frFac Zd (Formalism.L2.SG.Pf.locEqC_holds D Zd)
    (Formalism.L2.SG.Pf.locDiffC_holds D Zd) p F0 γ.lam hrow.2.1.1.fg hrow.2.2 hrow.2.1.2.2.2 hgP' b
  have hO := (Zd.agree p).2.2.2.1
  have hsg' : TermLoc.sgnP' D p b = TermLoc.sgnP D p b := by
    show (match (D.s.atP p).split with | some _ => TermLoc.sgnP D p b | none => (-1) ^ (D.R.rS - b.val)) = _
    rw [hsg]
  set c : (D.s.atP p).Ep := TermLoc.sgnP D p b * frFac Zd.δ p b with hc
  have hdiff : locF' Zd p F'₂ b - (tLoc Zd p γ).f b = c • baseChange₂ D p x := by
    show (TermLoc.sgnP' D p b * frFac Zd.δ p b) • baseChange₂ D p (frame F'₂ b) -
      (TermLoc.sgnP D p b * frFac Zd.δ p b) • baseChange₂ D p (frame (lf D F0) b) = _
    rw [hsg', hx, map_sub, smul_sub]
    rfl
  have hinv : (TermLoc.sgnP D p b * w) * c = 1 := by
    rw [hc, mul_mul_mul_comm, TermLoc.localSign_sq, hw1, one_mul]
  have hinvO : TermLoc.sgnP D p b * w ∈ (Zd.M p).L.O := by
    rw [hO]; exact (D.s.atP p).O.mul_mem (sgnP_mem p b) (by rw [← hO]; exact hw)

  have h1 : baseChange₂ D p x ∈ (locH Zd p).smulLat (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g'.q : (D.s.atP p).Fp))
      (lattice₂ D Zd.M p Λ₂) := by
    have : baseChange₂ D p x = (TermLoc.sgnP D p b * w) • (locF' Zd p F'₂ b - (tLoc Zd p γ).f b) := by
      rw [hdiff, smul_smul, hinv, one_smul]
    rw [this]
    exact Submodule.smul_mem _ ⟨_, hinvO⟩ hadm

  have hqg := Formalism.L2.SG.Pf.Cnt.DualityBasisChange.q_gS_inv_mem Zd.agree p hMs
  have h2 : (D.s.atP p).ιE (((gS D : ℕ) : D.host.E))⁻¹ • baseChange₂ D p x ∈ lattice₂ D Zd.M p Λ₂ := by
    have key : ∀ v ∈ (locH Zd p).smulLat (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g'.q : (D.s.atP p).Fp))
        (lattice₂ D Zd.M p Λ₂), (D.s.atP p).ιE (((gS D : ℕ) : D.host.E))⁻¹ • v ∈ lattice₂ D Zd.M p Λ₂ := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨y, hy, rfl⟩ := hv
        rw [smul_smul]
        exact (lattice₂ D Zd.M p Λ₂).smul_mem ⟨_, hqg⟩ hy
      | zero => rw [smul_zero]; exact Submodule.zero_mem _
      | add a c _ _ ha hc => rw [smul_add]; exact Submodule.add_mem _ ha hc
      | smul o v _ hv =>
        have e : (D.s.atP p).ιE (((gS D : ℕ) : D.host.E))⁻¹ • (o • v) =
            o • ((D.s.atP p).ιE (((gS D : ℕ) : D.host.E))⁻¹ • v) := by
          show _ • ((o : (D.s.atP p).Ep) • v) = (o : (D.s.atP p).Ep) • _
          rw [smul_smul, smul_smul, mul_comm]
        rw [e]; exact Submodule.smul_mem _ _ hv
    exact key _ h1
  have hg0 : ((gS D : ℕ) : D.host.E) ≠ 0 := by
    have := Formalism.L2.SG.Pf.Cnt.DualityBasisChange.gS_ne (D := D); exact_mod_cast this
  have h3 : baseChange₂ D p ((((gS D : ℕ) : D.host.E))⁻¹ • x) ∈ lattice₂ D Zd.M p Λ₂ := by
    rw [Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂]; exact h2
  haveI := p.isPrime
  letI := hlat
  have h4 := (Formalism.L2.SG.Pf.LocalDenominators.baseChangeAt_mem_localLattice_iff Zd p (Λ := Λ₂) (by infer_instance) _).1 h3
  obtain ⟨t, ht, htx⟩ := (Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF p.asIdeal Λ₂ _).1 h4
  refine ⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t, fun h => ht (by rw [← hPp]; exact h), ?_⟩
  have e : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t • x =
      ((gS D : ℕ) : 𝓞 D.host.E) • (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t • ((((gS D : ℕ) : D.host.E))⁻¹ • x)) := by
    rw [Formalism.L2.SG.Pf.LocalDenominators.oE_smul, Formalism.L2.SG.Pf.LocalDenominators.oE_smul, Formalism.L2.SG.Pf.LocalDenominators.oE_smul, smul_smul, smul_smul]
    congr 1
    push_cast
    field_simp
  change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t • x ∈ Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ₂
  rw [e]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) htx

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdCut

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}


variable (u') (F0) in
def GenXiRev : Prop :=
  ∀ (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (p : PlF D),
    IsRowLat D F0 Λ → AdmWit Λ (gS D) (lf D F0) F' 1 → IsLift Λ F' →
    (locH Zd p).IsGeneric ⟨lattice₂ D Zd.M p Λ, (locTerm Zd p Λ (lf D F0) F' (Tu D u) (Tu D u')).f, locF' Zd p F',
      (locTerm Zd p Λ (lf D F0) F' (Tu D u) (Tu D u')).T, (locTerm Zd p Λ (lf D F0) F' (Tu D u) (Tu D u')).T'⟩ →
    (locH Zd p).IsGeneric (locTerm Zd p Λ (lf D F0) F' (Tu D u) (Tu D u'))

theorem rowLat_of_move (hC : CtxP u u' F0 what₂) (γ : TermDef.Term D u u' F0 what₂) {Λ₂ : Submodule (𝓞 D.host.E) (VS D).V}
    {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ unipotentFrameFixers F0)
    (himg : (n : (VS D).V → (VS D).V) '' (Λ₂ : Set (VS D).V) = (γ.lam : Set (VS D).V)) : IsRowLat D F0 Λ₂ := by
  have hrow := hC.2.1.1 γ.lam γ.mem
  have hg : Formalism.HermitianLatticesTheory.gmap n Λ₂ = γ.lam := gmap_eq_of_image himg
  have hni : n⁻¹ ∈ Formalism.L2.SG.Pf.Cnt.StabilizerQuotient.G0 F0 := by
    refine ⟨(Formalism.HermitianLatticesTheory.isom _).inv_mem hn.1, fun a => ?_⟩
    refine Fin.lastCases ?_ (fun i => ?_) a
    · have h := hn.2.2.2.2
      simp only [FlagG.fvec, Fin.snoc_last]
      show n.symm _ = _
      rw [LinearEquiv.symm_apply_eq, h]
    · have h := hn.2.2.2.1 i
      simp only [FlagG.fvec, Fin.snoc_castSucc]
      show n.symm _ = _
      rw [LinearEquiv.symm_apply_eq, h]
  have h2 := Formalism.L2.SG.Pf.Cnt.StabilizerQuotient.rowLat_gmap ⟨n⁻¹, hni⟩ hrow
  have e : Formalism.HermitianLatticesTheory.gmap (n⁻¹ : (VS D).V ≃ₗ[D.host.E] (VS D).V) γ.lam = Λ₂ := by
    rw [← hg, ← Formalism.L2.SG.Pf.gmap_mul_sat, inv_mul_cancel, Formalism.L2.SG.Pf.gmap_one_sat]
  rw [← e]; exact h2

variable {Zd}

theorem btGen_of (hOK : BtOK Zd u u' F0 what₂) (hGX : GenXiRev Zd u' F0) : BtGen Zd u u' F0 what₂ := by
  intro hC γ Z F'₂ φ φ' Λ₂ hs
  have hLift := btLift_holds Zd hC γ Z F'₂ φ φ' Λ₂ hs
  have hAdm := btAdm Zd hC γ Z F'₂ φ φ' Λ₂ hs
  have hG := btG_holds Zd hC γ Z F'₂ φ φ' Λ₂ hs
  have hOKv := hOK hC γ Z F'₂ φ φ' Λ₂ hs
  obtain ⟨_, _, ⟨hlat, hloc⟩, ⟨n, hn, himg⟩⟩ := hs
  have hR := rowLat_of_move hC γ hn himg
  have hPD : PD D Λ₂ (lf D F0) u' (liftF F'₂) := ⟨hLift, ⟨1, hAdm⟩, hOKv⟩
  refine (Formalism.L2.SG.Pf.frameGenLoc_holds D Zd F0 Λ₂ (liftF F'₂) hR hPD
    (Formalism.L2.SG.Pf.m_plus_independent _ _ _ _) hG).2 fun p => ?_
  exact hGX Λ₂ (liftF F'₂) p hR hAdm hLift (hloc p).1

theorem bwdTerm'_of' (hOK : BtOK Zd u u' F0 what₂) (hGX : GenXiRev Zd u' F0) : BwdTerm' Zd u u' F0 what₂ :=
  bwdTerm'_of Zd (btLift_holds Zd) (btAdm Zd) (btG_holds Zd) hOK (btGen_of hOK hGX)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end
