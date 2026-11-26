module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ResidualIrreducibilityFormsEquivalent
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.NotLargeBaseConditionDisjoint
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfinityTypeEtaTildeAtCmTypeEmbeddingsEqHalf
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfinityTypeEtaTildeAtCmTypeEmbeddingsEqHalf
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.NPin GlobalTheory.NFacts

namespace GlobalTheory.EtaInfType

theorem main : ∀ (D : D7) (cf : CharFrame D) (C : NChoice D) (tp : TupTied D cf C), NCharTied D cf C tp → ∀ t, D.naut.infG D.naut.etaT (Formalism.L2.embT D t) = {(1 / 2 : ℂ)} := by
  intro D cf C tp N t
  have hI : (N.e1 D.naut.etaT).1.HasInfQ (embPsi D.host) (fun _ => (1 / 2 : ℚ)) := by
    rw [N.etaT]
    exact ⟨fun _ => 1, fun _ => by norm_num, cf.isEta.inf⟩
  have h1 := (N.infG _ _ hI (D.eTau t)).1
  have e0 : Formalism.L2.embT D t = embPsi D.host (D.eTau t) := rfl
  rw [e0, h1]
  push_cast
  rfl

end GlobalTheory.EtaInfType
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfinityTypeEtaTildeAtCmTypeEmbeddingsEqHalfStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.NPin GlobalTheory.NFacts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinityType_etaTilde_at_cmTypeEmbeddings_eq_half : ∀ (D : D7) (cf : CharFrame D) (C : NChoice D) (tp : TupTied D cf C), NCharTied D cf C tp → ∀ t, D.naut.infG D.naut.etaT (Formalism.L2.embT D t) = {(1 / 2 : ℂ)} := by
  first | exact @GlobalTheory.EtaInfType.main | exact GlobalTheory.EtaInfType.main | (intros; apply GlobalTheory.EtaInfType.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LinkedBundlePropertyAfterLargeBaseCoreProperty
noncomputable section

namespace GlobalTheory.NRows.AtPt

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.Inhab _root_.Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl
  GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.Fc NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem of_is {𝒮 : Slots} {K : Ctx} {q : WPt 𝒮 K} {D : D7} {O : Obj D} (h : q.Is D O) {r : ∀ D : D7, Obj D → Prop}
    (hr : r (q.w.D q.Z) q.O) : r D O :=
  (congrArg (fun x : Σ D : D7, Obj D => r x.1 x.2) h).mpr hr

theorem linkedBundleProperty_after_largeBaseCoreProperty {KP : BaseP} {Q Q' R : V4.Slot} {Bd : BdT} {Lk : LkT Bd} {E : Par → BdP Bd} (h : LargeBaseConditionG KP Q R)
    (he : RowE (sAnd Q' R) Lk E) : Lg1 KP Q Q' fun U => RowE U Lk E :=
  ⟨_, GlobalTheory.Fc.LgModel.largeBaseProperty_conditional (R := R),
    ((EvP.of_evGd h).and he).mono fun _ _ _ t β q c b l => t.2 β ⟨q.1, q.2 t.1⟩ c b l⟩

end GlobalTheory.NRows.AtPt

end
end
