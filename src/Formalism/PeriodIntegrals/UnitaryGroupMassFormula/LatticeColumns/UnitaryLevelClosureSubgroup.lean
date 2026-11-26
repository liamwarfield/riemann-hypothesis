module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.Development
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.StrongApproxN

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.UnitaryLevelClosureSubgroup
noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.PoincareInHH MeasureTheory

def KHg {D : D7} (X : HidaSetting D) (u : D.what₂.Word) :
    Subgroup (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) :=
  (Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).subgroupOf _

def unitaryLevelClosureSubgroup {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) :
    Subgroup (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) :=
  Subgroup.closure (Subtype.val ⁻¹' K2u X hb u)

def HaarRatio : Prop :=
  ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (K K' : Subgroup G), K' ≤ K → IsOpen (K' : Set G) →
    IsCompact (K : Set G) → (μ K).toReal / (μ K').toReal = (K'.relIndex K : ℝ)

def IdxGroupStep : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (_hK : X.LevelSubgroupCharacter) (u : D.what₂.Word),
    X.MeasTie hb → X.LevelSubgroupNormalized →
    ((unitaryLevelClosureSubgroup X hb u : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) =
      Subtype.val ⁻¹' K2u X hb u) ∧ unitaryLevelClosureSubgroup X hb u ≤ KHg X u

def IdxTopStep : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (_hK : X.LevelSubgroupCharacter) (u : D.what₂.Word),
    X.MeasTie hb → X.LevelSubgroupNormalized →
    IsTopologicalGroup (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) ∧
      BorelSpace (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) ∧
      IsOpen (unitaryLevelClosureSubgroup X hb u : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) ∧
      IsCompact (KHg X u : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)))

def IdxCountStep : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (_hK : X.LevelSubgroupCharacter) (u : D.what₂.Word),
    X.MeasTie hb → X.LevelSubgroupNormalized →
    ((unitaryLevelClosureSubgroup X hb u).relIndex (KHg X u) : ℝ) = ∏ p : TypX X, ((glkC D.R.k (gOf p) : ℝ) / (ukC D.R.k (gOf p) : ℝ))

theorem colsIdxStep_of (hH : HaarRatio) (h1 : IdxGroupStep) (h2 : IdxTopStep) (h3 : IdxCountStep) :
    ColsIdxStep := by
  intro D X hb hK u hM hL
  obtain ⟨hG, hK2⟩ := h1 X hb hK u hM hL
  obtain ⟨hT, hB, hO, hC⟩ := h2 X hb hK u hM hL
  have hHaar : (X.measW u).μHf.IsHaarMeasure := (X.measW_norm u).2.2.1
  have hr := @hH _ _ _ hT _ hB (X.measW u).μHf hHaar (KHg X u) (unitaryLevelClosureSubgroup X hb u) hK2 hO hC
  rw [← h3 X hb hK u hM hL, ← hr, hG]
  rfl

end PIW.MassDataColumns
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.HinfCpt
noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.PoincareInHH

def InfHAHomeo : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (hb : AdBridgeIso I), ∃ e : I.Ginf ≃ₜ* HA (Ainf I.F) I.cm.sig I.J,
    ∀ s, e s = (splitA I.cm.sig I.J (toHA I hb (s, 1))).1

def HStepInf : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (hb : AdBridgeIso I) (r : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E)
    (s : I.Ginf),
    (splitA I.cm.sig I.J (toHA I hb (s, 1))).1 ∈ Hsub (Ainf I.F) I.cm.sig I.J (⟨e, f, z⟩ : Frame I.E I.n r) ↔
      s ∈ Hset I (Set.range e ∪ Set.range f ∪ {z})

def HinfCompactBundle : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word),
    IsCompact ((PoincareSetting.Hinf X u : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf)

theorem hinfCompact_of (h0 : ∀ I : Formalism.MainNotions.S.AutInst, AdBridgeIso I) (h1 : InfHAHomeo) (h2 : HStepInf)
    (h3 : HinfCompactBundle) : MassDataMassesW.HinfCompact := by
  intro D X u
  obtain ⟨e, he⟩ := h1 X.B.I (h0 X.B.I)
  have key : ∀ s : X.B.I.Ginf, e s ∈ Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) ↔
      s ∈ (PoincareSetting.Hinf X u : Set X.B.I.Ginf) := by
    intro s
    rw [he s]
    exact h2 X.B.I (h0 X.B.I) D.R.rS (frameOf X u).e (frameOf X u).f (frameOf X u).z s
  have hset : (Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) :
      Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)) = e '' (PoincareSetting.Hinf X u : Set X.B.I.Ginf) := by
    ext x
    constructor
    · intro hx
      refine ⟨e.symm x, (key _).1 ?_, e.apply_symm_apply x⟩
      rwa [e.apply_symm_apply]
    · rintro ⟨s, hs, rfl⟩
      exact (key s).2 hs
  have hc : IsCompact (Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) :
      Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)) := by
    rw [hset]
    exact (h3 X u).image e.toHomeomorph.continuous
  exact isCompact_iff_compactSpace.mp hc

end PIW.MassDataColumns
end
end
