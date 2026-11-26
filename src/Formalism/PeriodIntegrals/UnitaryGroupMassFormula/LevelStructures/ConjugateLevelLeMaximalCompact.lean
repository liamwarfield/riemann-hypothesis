module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.GlobLevelS

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.ConjugateLevelLeMaximalCompact
noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge

variable {D : D7}

def idxS (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (w : D.what₂.Word) (p : TypX X) : ℕ :=
  (Subgroup.closure (Subtype.val ⁻¹' compSet X.B.I.cm.sig X.B.I.J (K2u X hb w) p.1 :
      Set (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w)))).relIndex
    (Subgroup.closure (Subtype.val ⁻¹' Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 :
      Set (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))))

def idxHp (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (w : D.what₂.Word) (p : TypX X) : ℕ :=
  (Subgroup.closure (Subtype.val ⁻¹' compSet X.B.I.cm.sig X.B.I.J (K2u X hb w) p.1 :
      Set (Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w)))).relIndex
    (Subgroup.closure (Subtype.val ⁻¹' Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 :
      Set (Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))))

def idxH (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (w : D.what₂.Word) : ℕ :=
  (Subgroup.closure (Subtype.val ⁻¹' K2u X hb w : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w)))).relIndex
    (Subgroup.closure (Subtype.val ⁻¹' (Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :
      Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))))

def HaarIdxLoc : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.LevelSubgroupCharacter → X.MeasTie hb → X.LevelSubgroupNormalized →
    ∀ (w : D.what₂.Word) (p : TypX X), muSv X w p = (idxS X hb w p : ℝ) * muSvpp X hb w p

def HaarIdxGlob : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.LevelSubgroupCharacter → X.MeasTie hb → X.LevelSubgroupNormalized →
    ∀ w : D.what₂.Word, muHf X w = (idxH X hb w : ℝ) * muHfpp X hb w

def LocLevi : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.LevelSubgroupCharacter → X.MeasTie hb → X.LevelSubgroupNormalized →
    ∀ (w : D.what₂.Word) (p : TypX X), idxS X hb w p = idxHp X hb w p

def GlobProd : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.LevelSubgroupCharacter → X.MeasTie hb → X.LevelSubgroupNormalized →
    ∀ w : D.what₂.Word, idxH X hb w = ∏ p : TypX X, idxHp X hb w p

def ConjugateLevelLeMaximalCompact : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.LevelSubgroupCharacter → X.LevelSubgroupNormalized →
    ∀ w : D.what₂.Word, K2u X hb w ⊆ (Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :
      Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J))

theorem ratioH_of (h1 : HaarIdxLoc) (h2 : HaarIdxGlob) (h3 : LocLevi) (h4 : GlobProd) : RatioH := by
  intro D X hb hK hM hL w
  rw [h2 X hb hK hM hL w, h4 X hb hK hM hL w]
  simp only [h1 X hb hK hM hL w, h3 X hb hK hM hL w, Finset.prod_mul_distrib]
  push_cast
  ring

end MassDataLevelSSteps
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.GlobLevelSOf
noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.Volumes

def CMInst : Prop :=
  ∀ {D : D7} (X : HidaSetting D), IsCMExt X.B.I.F X.B.I.E X.B.I.cm.sig ∧ IsHermND X.B.I.cm.sig X.B.I.J

def FrameStd : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (w : D.what₂.Word), ∃ T : X.B.I.F,
    (frameOf X w).IsStd X.B.I.cm.sig X.B.I.J T

def LatAdapted : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (w : D.what₂.Word), ∃ ΛX ΛW ΛY : Set (Fin X.B.I.n → X.B.I.E),
    Adapted X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J (frameOf X w) ΛX ΛW ΛY ∧
    Kf X.B.I.cm.sig X.B.I.J (ΛX ∪ ΛW ∪ ΛY) = Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))

def ProdNH : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (w : D.what₂.Word),
    IsProdNH X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J (Ssub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))
      (Nsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w)) (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))
      (X.measW w).μSf (X.measW w).μNf (X.measW w).μHf

def GlobFromParts : Prop := LevelSAll → CMInst → FrameStd → LatAdapted → ProdNH → GlobLevelS

end MassDataLevelSSteps
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.TypedNeOf
noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge

def KSpCompact : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (w : D.what₂.Word) (p : TypX X),
    IsCompact (Subtype.val ⁻¹' Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 :
      Set (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w)))

def KSpOpen : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (w : D.what₂.Word) (p : TypX X),
    IsOpen (Subtype.val ⁻¹' Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 :
      Set (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w)))

theorem typedNe_of (h1 : KSpCompact) (h2 : KSpOpen) : TypedNe := by
  intro D X hb _ _ w p
  have hH : ((X.measW w).μSv p.1).IsHaarMeasure := (X.measW_norm w).2.2.2.2.2.2.2.1 p.1
  have hne : (Subtype.val ⁻¹' Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 :
      Set (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))).Nonempty :=
    ⟨1, (Kloc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).one_mem⟩
  unfold muSv
  exact (ENNReal.toReal_pos (hH.toIsOpenPosMeasure.open_pos _ (h2 X w p) hne)
    (hH.toIsFiniteMeasureOnCompacts.lt_top_of_isCompact (h1 X w p)).ne).ne'

end MassDataLevelSSteps
end
end
