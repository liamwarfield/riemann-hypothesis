module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaLiftGeneralLinear
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.GoodRef
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AlIsRecrecLaws

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtRows
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.LiftRef
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 _root_.Formalism.L2.Host _root_.Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2
  GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
def ForallRowSideParameters (hL : _root_.UpperTheory.Zero.LLC.RecTExists)
    (q : ∀ (D : D7) (cf : CharFrame D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (Rw : RowSide D), _root_.GlobalTheory.HeightCounting.Up.ParityConditions hL D cf rep Rw →
      MtFam D → Prop) : Prop :=
  OverRows fun _ _ _ _ w Z _ _ _ _ Y => ∀ Rw (a : _root_.GlobalTheory.HeightCounting.Up.ParityConditions hL (w.st Z).toD7 (TC.cf w.I w.l Z) (repOf Y) Rw) (M : MtFam (w.st Z).toD7) tup Q,
    MtAd Y M → MtInput (w.st Z).toD7 M tup Q → q (w.st Z).toD7 (TC.cf w.I w.l Z) (repOf Y) Rw a M
end GlobalTheory.LiftRef
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MGoodRef
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.One.M.B
end UpperTheory.One.M.B
open UpperTheory.One.M.B in
theorem UpperTheory.One.M.goodRef_alt :
    _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.LiftRef.ForallRowSideParameters hL fun D _ _ _ a M => ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (S : Submodule ℂ (Formalism.AUTREP.GAf D.host.E D.R.nV → (M D.what₂.mu0 j h1 h2).wt.W)) (hS : NG.IsIrrRep (M D.what₂.mu0 j h1 h2).wt.ρ S), (NG.isoTyp (M D.what₂.mu0 j h1 h2).wt.ρ S).comap (M D.what₂.mu0 j h1 h2).real ≠ ⊥ → UpperTheory.One.M.GoodAU (GlobalTheory.LiftRef.autOf (M D.what₂.mu0 j h1 h2) S hS) := by
  intro _ hL
  unfold _root_.GlobalTheory.LiftRef.ForallRowSideParameters
  refine GlobalTheory.LiftRef.overRows_and_mono levSplit levSplit (fun K B f T w Z Wt hX z p0 Y h' _ => ?_)
  intro Rw a M tup Q hMA _ j h1 h2 S hS hne s σ hσ
  obtain ⟨i, rfl⟩ : ∃ i : Fin (w.st Z).toD7.R.m, i.1 + 1 = j := ⟨⟨j - 1, by omega⟩, by simp only; omega⟩
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 hne
  have hry : (M _ _ h1 h2).real y ≠ 0 := fun e =>
    hy0 ((M _ _ h1 h2).real_inj (e.trans (map_zero _).symm))
  obtain ⟨f', hf', hf0', hff'⟩ := GlobalTheory.AutUnr.exists_fixed_of_isoTyp _ hS.1.stable
    {κ | κ ∈ Umax (w.st Z).toD7.host.E (w.st Z).toD7.R.nV ∧ TrivOutside {s.v} κ ∧ (s.v ∈ gPl (w.st Z).toD7 → IsPrincipalCongruenceAt s κ)} hy hry
    (fun κ hκ => GlobalTheory.SphInertRef.rt_real_eq_of_lev hMA i y κ (h' i (hMA.PV i) (hMA.std i) s κ hκ.1 hκ.2.1 hκ.2.2).1
      (h' i (hMA.PV i) (hMA.std i) s κ hκ.1 hκ.2.1 hκ.2.2).2)
  exact good_of_fix _ S hS s (fun hg => GlobalTheory.SplitTypeCompl.exists_padic_equiv _ s hg) f' hf' hf0'
    (fun κ a b c => hff' κ ⟨a, b, c⟩) σ hσ
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BaseChangeLocalLanglandsAtTrivialTwist
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsLocallySplitLift
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalComponentMatchesOfHoweDuality
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SplitReferencePairOfTrivialMu
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLiftOfReference
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin
open GlobalTheory.RefPair
theorem GlobalTheory.RefTheta.locComp_of_isRc_classMapD_cenLoc : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.LiftRef.ForallRowSideParameters hL fun D cf rep _ _ M => ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), ∃ X : RowMod D rep j, HasThetaAt D (M D.what₂.mu0 j h1 h2) X (cf.mu0 ⟨j - 1, by omega⟩) cf.eta := by
  intro hN hL
  unfold _root_.GlobalTheory.LiftRef.ForallRowSideParameters OverRows
  refine GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun K B f T _ w _ Z Wt hX z p0 Y hH hEx _ _ _ Rw a M tup Q hMA _ j h1 h2 => ?_
  obtain ⟨i, rfl⟩ : ∃ i : Fin (w.st Z).toD7.R.m, j = (i : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp only; omega⟩
  have hC : z.R.C = TC.cf w.I w.l Z := z.lev.C
  obtain ⟨X, hX⟩ := GlobalTheory.RefTheta.datum_real hN.hc hN.decay _ _ _ _ _ _ _ z.R z.F z.cG p0 Y z.pins hH hEx M hMA i
  refine ⟨X, ?_⟩
  rw [← hC]
  exact hX
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin
open GlobalTheory.RefPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_theta_at_of_third_layer : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.LiftRef.ForallRowSideParameters hL fun D cf rep _ _ M => ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), ∃ X : RowMod D rep j, HasThetaAt D (M D.what₂.mu0 j h1 h2) X (cf.mu0 ⟨j - 1, by omega⟩) cf.eta := by
  first | exact @_root_.GlobalTheory.RefTheta.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.RefTheta.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.RefTheta.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin
noncomputable section
namespace GlobalTheory.RefPair
end GlobalTheory.RefPair
namespace GlobalTheory.RefPair
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin
set_option maxHeartbeats 1000000 in
theorem referencePair_split_of_mu_eq_zero_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.LiftRef.ForallRowSideParameters hL fun D cf rep _ _ M => ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (σ : D.what₂.FT) (S : Submodule ℂ (Formalism.AUTREP.GAf D.host.E D.R.nV → (M D.what₂.mu0 j h1 h2).wt.W)), NG.IsIrrRep (M D.what₂.mu0 j h1 h2).wt.ρ S → (∃ y ∈ D.what₂.isot j σ, ∃ F ∈ (NG.isoTyp (M D.what₂.mu0 j h1 h2).wt.ρ S).comap (M D.what₂.mu0 j h1 h2).real, inner ℂ F (D.what₂.thetaT D.what₂.mu0 j y) ≠ 0) → ∀ (s : SplitPlace D.host.E) (π : GlobalTheory.SmGL.IrrRep (GL (Fin (D.R.r + D.R.t)) (s.w.adicCompletion D.host.E))) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.r) (s.w.adicCompletion D.host.E))), IsLocS (n := D.R.nV) S s π → IsLocS (rep σ).S s τ → GlobalTheory.ThetaGL.ThetaPair ((cf.mu0 ⟨j - 1, by omega⟩).loc s.w) τ.ρ (GlobalTheory.SmGL.twist π.ρ (GlobalTheory.SmGL.detChar (Fin (D.R.r + D.R.t)) (cf.eta.loc s.w))) := by
  intro hN hL
  have hA := _root_.GlobalTheory.T.exists_theta_at_of_third_layer hN hL
  unfold _root_.GlobalTheory.LiftRef.ForallRowSideParameters at hA ⊢
  refine GlobalTheory.LiftRef.overRows_and_mono hA hA ?_
  intro K B f T w Z Wt hX z p0 Y hA1 _ Rw a M tup Q hMA hMI j h1 h2 σ S hS hPair s π τ hπ hτ
  obtain ⟨X, hXd⟩ := hA1 Rw a M tup Q hMA hMI j h1 h2
  obtain ⟨Bf, k1, k2, k3, k4⟩ := GlobalTheory.RowSphSmall.exists_form_rowRepR hN.hc hN.decay _ _ _ _ _ _ _ z.R z.F z.cG p0 Y z.pins σ
  exact thetaPair_of_hasThetaAt hN.what₂.bz _ _ X _ _ hXd σ S hS hPair s π τ hπ hτ
    (GlobalTheory.RowSphSmall.isUnitarisable_of_isLocS _ Bf k1 k2 k3 k4 s τ hτ)
end GlobalTheory.RefPair
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_reference_pair_of_trivial_mu_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.LiftRef.ForallRowSideParameters hL fun D cf rep _ _ M => ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (σ : D.what₂.FT) (S : Submodule ℂ (Formalism.AUTREP.GAf D.host.E D.R.nV → (M D.what₂.mu0 j h1 h2).wt.W)), NG.IsIrrRep (M D.what₂.mu0 j h1 h2).wt.ρ S → (∃ y ∈ D.what₂.isot j σ, ∃ F ∈ (NG.isoTyp (M D.what₂.mu0 j h1 h2).wt.ρ S).comap (M D.what₂.mu0 j h1 h2).real, inner ℂ F (D.what₂.thetaT D.what₂.mu0 j y) ≠ 0) → ∀ (s : SplitPlace D.host.E) (π : GlobalTheory.SmGL.IrrRep (GL (Fin (D.R.r + D.R.t)) (s.w.adicCompletion D.host.E))) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.r) (s.w.adicCompletion D.host.E))), IsLocS (n := D.R.nV) S s π → IsLocS (rep σ).S s τ → GlobalTheory.ThetaGL.ThetaPair ((cf.mu0 ⟨j - 1, by omega⟩).loc s.w) τ.ρ (GlobalTheory.SmGL.twist π.ρ (GlobalTheory.SmGL.detChar (Fin (D.R.r + D.R.t)) (cf.eta.loc s.w))) := by
  first | exact @_root_.GlobalTheory.RefPair.referencePair_split_of_mu_eq_zero_alt | exact _root_.GlobalTheory.RefPair.referencePair_split_of_mu_eq_zero_alt | (intros; apply _root_.GlobalTheory.RefPair.referencePair_split_of_mu_eq_zero_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsUnitarizableOfFiniteTypeOfLocalComponents
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin
namespace GlobalTheory.RowSplitUnit
set_option maxHeartbeats 2000000 in
theorem isUnitarizable_of_finiteType_of_local_components_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.LiftRef.ForallRowSideParameters hL fun D _ rep _ _ _ => ∀ (j : ℕ) (σ : D.what₂.FT), D.what₂.isot j σ ≠ ⊥ → ∀ s : SplitPlace D.host.E, ∃ τ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.r) (s.w.adicCompletion D.host.E)), IsLocS (rep σ).S s τ ∧ GlobalTheory.SmGL.IsUnitarisable τ.ρ := by
  intro hN hL
  unfold _root_.GlobalTheory.LiftRef.ForallRowSideParameters
  refine EvG.imp (evG_of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev) fun K _ _ _ _ hHost => ?_
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp, ?_⟩
  intro B f T hO _ _ _ _ w _ Z Wt hX z p0 Y hHo _ _ _ _ Rw _ M tup Q _ _ j σ _ s
  obtain ⟨hH, hF, -⟩ := hHost (w.st Z) hO
  obtain ⟨τ, hτ⟩ := GlobalTheory.RowLocalRows2.finTyp_rows_exists_isLocS hN.hc hN.decay _ _ _ _ _ _ _ z.R z.F z.cG p0 Y z.pins hHo hH hF σ s
  obtain ⟨Bf, k1, k2, k3, k4⟩ := GlobalTheory.RowSphSmall.exists_form_rowRepR hN.hc hN.decay _ _ _ _ _ _ _ z.R z.F z.cG p0 Y z.pins σ
  exact ⟨τ, hτ, GlobalTheory.RowSphSmall.isUnitarisable_of_isLocS _ Bf k1 k2 k3 k4 s τ hτ⟩
end GlobalTheory.RowSplitUnit
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitarisable_local_component_at_split : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.LiftRef.ForallRowSideParameters hL fun D _ rep _ _ _ => ∀ (j : ℕ) (σ : D.what₂.FT), D.what₂.isot j σ ≠ ⊥ → ∀ s : SplitPlace D.host.E, ∃ τ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.r) (s.w.adicCompletion D.host.E)), IsLocS (rep σ).S s τ ∧ GlobalTheory.SmGL.IsUnitarisable τ.ρ := by
  first | exact @_root_.GlobalTheory.RowSplitUnit.isUnitarizable_of_finiteType_of_local_components_alt | exact _root_.GlobalTheory.RowSplitUnit.isUnitarizable_of_finiteType_of_local_components_alt | (intros; apply _root_.GlobalTheory.RowSplitUnit.isUnitarizable_of_finiteType_of_local_components_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocGRankOne
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin
noncomputable section
namespace GlobalTheory.LiftSplitLoc
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands in
theorem locG_rankOne_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {cf : CharFrame D} (T : GlobalTheory.RowTie.WDTie D.nd D.naut)
    (cg : _root_.GlobalTheory.HeightCounting.CGTrueT hL D T) (cs : CharSide D cf) (π : D.naut.CG 1) (w : PlE D.host)
    (ξ : (w.adicCompletion D.host.E)ˣ →* ℂˣ) (h : IsComp (cs.e1 π).1 w ξ) :
    T.e w (D.naut.locG π w) = _root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D w 1 (Irr.ofDet 1 ξ h.1) := by
  have := host_isCMField D.host
  set χ' := (CGu.equivChar D.host.E (cg.e 1 π)).1 with hχ'
  set χ := (cs.e1 π).1 with hχ
  have hloc (v : PlE D.host) : T.e v (D.naut.locG π v) =
      ParLawsT.locParT hL (CG.ofChar χ') (D.nd.plOm.2 v) := by
    rw [hχ', CGu.ofChar_equivChar]
    exact cg.loc 1 π v
  have unr' (v : PlE D.host) : D.naut.unr (D.naut.locG π v) ↔ χ'.UnrAt v := by
    rw [T.unr v (D.naut.locG π v), hloc v]
    exact _root_.GlobalTheory.RankOneComp.locParT_ofChar_unr_iff_unrAt hL χ' (D.nd.plOm.2 v)
  have hchar : χ' = χ := by
    rw [← mul_inv_eq_one]
    apply GlobalTheory.HeckeSplitRow.eq_one_of_split D.host
    filter_upwards [D.naut.locG_unr_ae π] with v hv _
    have u1 := (cs.unr_iff π v).1 hv
    have u2 := (unr' v).1 hv
    refine ⟨fun x hx => ?_, ?_⟩
    · change χ'.loc v x * (χ.loc v x)⁻¹ = 1
      rw [u2 x hx, u1 x hx, inv_one, mul_one]
    · have hf := cs.frob π v u1
      have hf' : D.naut.frobEig (D.naut.locG π v) = {(((χ'.val v)⁻¹ : ℂˣ) : ℂ)} := by
        rw [T.frobEig _ _ hv, hloc v]; exact _root_.GlobalTheory.RankOneComp.frobEig_locParT_ofChar_of_unrAt hL χ' _ u2
      rw [hf', Multiset.singleton_inj, Units.val_inj, inv_inj] at hf
      rw [HChar.val_mul, HChar.val_inv, hf, mul_inv_cancel]
  have hcomp : IsComp χ w (χ.loc w) := ⟨ParLaws.isSmoothChar_loc χ w, fun _ => rfl⟩
  obtain ⟨ξ₀, -, huniq, -⟩ := GlobalTheory.T.heckeChar_localComponent_exists_unique_unitary D.host.E χ w
  have hξ : ξ = χ.loc w := (huniq _ h).trans (huniq _ hcomp).symm
  subst hξ
  rw [hloc, _root_.GlobalTheory.CuspRep.ParLaws.local_parameter_of_hecke_character_eq_reciprocity, _root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep]
  rw [hchar]
  rfl
end GlobalTheory.LiftSplitLoc
namespace GlobalTheory.LiftSplitLoc
end GlobalTheory.LiftSplitLoc
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin
noncomputable section
noncomputable section
namespace UpperTheory.One.M
theorem localComponent_matches_of_howeDuality_alt (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) (hB : GlobalTheory.Published.BernsteinUnitaryProductIrreducible)
 (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {D : D7} {cf : CharFrame D}
    {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} {Rw : RowSide D} (a : _root_.GlobalTheory.HeightCounting.Up.ParityConditions hL D cf rep Rw) (j : ℕ) (h1 : 1 ≤ j)
    (h2 : j ≤ D.R.m) (σ : D.what₂.FT) (P : NG.AutRep D.host.E D.R.nV) (μ : D.naut.CG 1)
    (hμ : (a.chr.e1 μ).1 = cf.mu0 ⟨j - 1, by omega⟩) (s : SplitPlace D.host.E)
    (π : IrrRep (GL (Fin (D.R.r + D.R.t)) (s.w.adicCompletion D.host.E)))
    (τ : IrrRep (GL (Fin D.R.r) (s.w.adicCompletion D.host.E))) (hπ : IsLocS (n := D.R.nV) P.S s π)
    (hτ : IsLocS (rep σ).S s τ) (hU : IsUnitarisable τ.ρ)
    (hP : ThetaPair ((cf.mu0 ⟨j - 1, by omega⟩).loc s.w) τ.ρ
      (GlobalTheory.SmGL.twist π.ρ (GlobalTheory.SmGL.detChar (Fin (D.R.r + D.R.t)) (cf.eta.loc s.w))))
    (hgπ₀ : UpperTheory.Zero.LLC.Good (GlobalTheory.LocLanglands.cls π)) :
    D.nbc.locAU j (a.A.cls j h1 h2 P) s.w =
      D.naut.lpChar (D.naut.lpSum (Rw.locR σ s.w) (spehLoc D.nd D.naut ⟨1, μ, D.R.t⟩ s.w))
        (D.naut.locG D.naut.etaTinv s.w) := by
  classical
  have := GlobalTheory.CuspRep.host_isCMField D.host
  have L : _root_.UpperTheory.One.M.RecLawsH (_root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D s.w) := (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 s.w)).recLaws
  set χ := cf.mu0 ⟨j - 1, by omega⟩ with hχ
  have hμc : IsComp χ s.w (χ.loc s.w) := ⟨GlobalTheory.CuspRep.ParLaws.isSmoothChar_loc χ s.w, fun _ => rfl⟩
  obtain ⟨ξ₀, -, huniq, hunit⟩ := GlobalTheory.T.heckeChar_localComponent_exists_unique_unitary D.host.E χ s.w
  have hχu : χ.IsUnitary := hμ ▸ (a.chr.e1 μ).2
  have hμU : IsUnitaryChar (χ.loc s.w) := fun x => by
    rw [huniq _ hμc]; exact hunit hχu x
  have hηc : IsComp cf.eta s.w (cf.eta.loc s.w) := ⟨GlobalTheory.CuspRep.ParLaws.isSmoothChar_loc cf.eta s.w, fun _ => rfl⟩
  have hηi : IsComp (a.chr.e1 D.naut.etaTinv).1 s.w ((cf.eta⁻¹).loc s.w) := by
    rw [a.chr.etaTinv]
    exact ⟨GlobalTheory.CuspRep.ParLaws.isSmoothChar_loc _ s.w, fun _ => rfl⟩
  have hinv : (cf.eta⁻¹).loc s.w = (cf.eta.loc s.w)⁻¹ := MonoidHom.ext fun _ => rfl
  have hrt : D.R.r < D.R.t := by
    have := D.R.rank_add_five_le
    unfold Ranks.r
    omega
  let π₀ : Irr (s.w.adicCompletion D.host.E) (D.R.r + D.R.t) := Irr.ofIrrRep π
  let π' := GlobalTheory.SplitPairLift.twistIrr π₀ hηc.1
  let τ₀ : Irr (s.w.adicCompletion D.host.E) D.R.r := Irr.ofIrrRep τ
  let cμ := Irr.ofDet 1 (χ.loc s.w) hμc.1
  let τμ := GlobalTheory.SplitPairLift.detIrr D.R.t hμc.1
  let cη := Irr.ofDet 1 ((cf.eta⁻¹).loc s.w) hηi.1
  have e1 : Nonempty (π'.π.Equiv (prod₂ τ₀.π τμ.π)) :=
    _root_.GlobalTheory.T.theta_lift_general_linear hBZ hB _ D.R.r D.R.t _ _ _ τ.ρ π'.π hrt hμc.1 hμU τ.smooth τ.irr hU π'.smooth π'.irr hP
  have e2 := L.prod _ _ τ₀ τμ π' e1
  have e3 := L.det D.R.t _ cμ τμ ⟨.refl _⟩ ⟨.refl _⟩
  have hgπ : GoodI π' := by
    have e : GlobalTheory.LocLanglands.cls (⟨π'.V, π'.π, π'.smooth, π'.irr⟩ : IrrRep (GL (Fin (D.R.r + D.R.t)) (s.w.adicCompletion D.host.E))) =
        (GlobalTheory.LocLanglands.cls (⟨π₀.V, π₀.π, π₀.smooth, π₀.irr⟩ : IrrRep (GL (Fin (D.R.r + D.R.t)) (s.w.adicCompletion D.host.E)))).tw (cf.eta.loc s.w) hηc.1 :=
      (GlobalTheory.LocGL.IrrGL.tw_of π₀.π π₀.smooth π₀.irr (cf.eta.loc s.w) hηc.1).symm
    show UpperTheory.Zero.LLC.Good _
    rw [e]
    exact (GlobalTheory.RecT.good_tw_iff _ _ _).2 hgπ₀
  have e4 := _root_.UpperTheory.One.M.RecLawsH.twist L _ (cf.eta.loc s.w)⁻¹ cη π' π₀ hgπ (by rw [← hinv]; exact ⟨.refl _⟩) (by
    show Nonempty (π₀.π.Equiv (GlobalTheory.SmGL.twist (GlobalTheory.SmGL.twist π₀.π (GlobalTheory.SmGL.detChar _ (cf.eta.loc s.w))) (GlobalTheory.SmGL.detChar _ (cf.eta.loc s.w)⁻¹)))
    rw [GlobalTheory.SplitPairLift.twist_twist_inv]
    exact ⟨.refl _⟩)
  have hμi : IsComp (a.chr.e1 μ).1 s.w (χ.loc s.w) := by
    rw [hμ]
    exact hμc
  have eμ : a.T.e s.w (D.naut.locG μ s.w) = GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D s.w 1 cμ :=
    GlobalTheory.LiftSplitLoc.locG_rankOne_alt a.T a.cg a.chr μ s.w (χ.loc s.w) hμi
  have eη : a.T.e s.w (D.naut.locG D.naut.etaTinv s.w) = GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D s.w 1 cη :=
    GlobalTheory.LiftSplitLoc.locG_rankOne_alt a.T a.cg a.chr D.naut.etaTinv s.w ((cf.eta⁻¹).loc s.w) hηi
  have hau : a.T.e s.w (D.nbc.locAU j (a.A.cls j h1 h2 P) s.w) = _root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D s.w _ π₀ := a.au j h1 h2 P s π hπ
  have hrow : a.T.e s.w (Rw.locR σ s.w) = _root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D s.w _ τ₀ := a.row.1 σ s τ hτ
  have h7 : D.naut.lpDim (D.naut.locG D.naut.etaTinv s.w) = 1 := by
    rw [← a.T.dim, eη, L.dim]
  apply (a.T.e s.w).injective
  rw [a.T.char _ _ _ h7, a.T.sum, GlobalTheory.SplitPairLift.e_spehLoc, hau, hrow, e4, e2, e3, eη, eμ]
set_option maxHeartbeats 1000000 in
theorem liftSplitLocal_of_howeDuality_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.LiftRef.ForallRowSideParameters hL fun D cf _ Rw a M => ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (σ : D.what₂.FT) (S : Submodule ℂ (Formalism.AUTREP.GAf D.host.E D.R.nV → (M D.what₂.mu0 j h1 h2).wt.W)) (hS : NG.IsIrrRep (M D.what₂.mu0 j h1 h2).wt.ρ S), (∃ y ∈ D.what₂.isot j σ, ∃ F ∈ (NG.isoTyp (M D.what₂.mu0 j h1 h2).wt.ρ S).comap (M D.what₂.mu0 j h1 h2).real, inner ℂ F (D.what₂.thetaT D.what₂.mu0 j y) ≠ 0) → ∀ μ : D.naut.CG 1, (a.chr.e1 μ).1 = cf.mu0 ⟨j - 1, by omega⟩ → ∀ w, IsSplitPl D.host w → D.nbc.locAU j (a.A.cls j h1 h2 (GlobalTheory.LiftRef.autOf (M D.what₂.mu0 j h1 h2) S hS)) w = D.naut.lpChar (D.naut.lpSum (Rw.locR σ w) (spehLoc D.nd D.naut ⟨1, μ, D.R.t⟩ w)) (D.naut.locG D.naut.etaTinv w) := by
  intro hP hL
  have hA := _root_.GlobalTheory.T.split_reference_pair_of_trivial_mu_alt hP hL
  have hB := _root_.GlobalTheory.T.exists_unitarisable_local_component_at_split hP hL
  have hC := _root_.UpperTheory.One.M.goodRef_alt hP hL
  unfold _root_.GlobalTheory.LiftRef.ForallRowSideParameters at hA hB hC ⊢
  refine GlobalTheory.LiftRef.overRows_and_mono (GlobalTheory.LiftRef.overRows_and_mono hA hB fun _ _ _ _ _ _ _ _ _ _ _ a b => And.intro a b) hC fun K B f T w Z Wt hX z p0 Y HAB HC Rw a M tup Q hM hI j h1 h2 σ S hS hpair μ hμ v hv => ?_
  obtain ⟨HA, HB⟩ := HAB
  obtain ⟨s, rfl⟩ := GlobalTheory.PairReadPf.exists_splitPlace_w _ v hv
  have hne : (w.st Z).toD7.what₂.isot j σ ≠ ⊥ := by
    obtain ⟨y, hy, F, -, hF⟩ := hpair
    intro hb
    rw [hb, Submodule.mem_bot] at hy
    apply hF
    rw [hy, map_zero, inner_zero_right]
  obtain ⟨τ, hτ, hU⟩ := HB Rw a M tup Q hM hI j σ hne s
  obtain ⟨π, hπ⟩ := GlobalTheory.LocCompSplit.exists_isLocS (GlobalTheory.LiftRef.autOf (M _ j h1 h2) S hS) s
  have hne' : (NG.isoTyp (M _ j h1 h2).wt.ρ S).comap (M _ j h1 h2).real ≠ ⊥ := by
    obtain ⟨y, hy, F, hF, hF0⟩ := hpair
    intro hb
    rw [hb, Submodule.mem_bot] at hF
    subst hF
    exact hF0 (inner_zero_left _)
  exact _root_.UpperTheory.One.M.localComponent_matches_of_howeDuality_alt hP.what₂.bz hP.what₂.bern hL a j h1 h2 σ _ μ hμ s π τ hπ hτ hU
    (HA Rw a M tup Q hM hI j h1 h2 σ S hS hpair s π τ hπ hτ) (HC Rw a M tup Q hM hI j h1 h2 S hS hne' s π hπ)
end UpperTheory.One.M
end
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin
noncomputable section
namespace GlobalTheory.LiftSplitLoc
end GlobalTheory.LiftSplitLoc
namespace GlobalTheory.LiftSplitLoc
end GlobalTheory.LiftSplitLoc
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_locally_split_lift_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.LiftRef.ForallRowSideParameters hL fun D cf _ Rw a M => ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (σ : D.what₂.FT) (S : Submodule ℂ (Formalism.AUTREP.GAf D.host.E D.R.nV → (M D.what₂.mu0 j h1 h2).wt.W)) (hS : NG.IsIrrRep (M D.what₂.mu0 j h1 h2).wt.ρ S), (∃ y ∈ D.what₂.isot j σ, ∃ F ∈ (NG.isoTyp (M D.what₂.mu0 j h1 h2).wt.ρ S).comap (M D.what₂.mu0 j h1 h2).real, inner ℂ F (D.what₂.thetaT D.what₂.mu0 j y) ≠ 0) → ∀ μ : D.naut.CG 1, (a.chr.e1 μ).1 = cf.mu0 ⟨j - 1, by omega⟩ → ∀ w, IsSplitPl D.host w → D.nbc.locAU j (a.A.cls j h1 h2 (GlobalTheory.LiftRef.autOf (M D.what₂.mu0 j h1 h2) S hS)) w = D.naut.lpChar (D.naut.lpSum (Rw.locR σ w) (spehLoc D.nd D.naut ⟨1, μ, D.R.t⟩ w)) (D.naut.locG D.naut.etaTinv w) := by
  first | exact @_root_.UpperTheory.One.M.liftSplitLocal_of_howeDuality_alt | exact _root_.UpperTheory.One.M.liftSplitLocal_of_howeDuality_alt | (intros; apply _root_.UpperTheory.One.M.liftSplitLocal_of_howeDuality_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReferenceLiftInjective
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.LiftRef.UpInjRows
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix _root_.Formalism.L2.Theta _root_.Formalism.L2.DIV _root_.Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.RecTie Formalism.IndefR.Lev
theorem locComp_of_isRc_classMapD_cenLoc : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.LiftRef.ForallRowSideParameters hL fun D _ _ _ _ _ => ∀ (j : ℕ) (_ : 1 ≤ j) (_ : j ≤ D.R.m) (σ : D.what₂.FT), ∀ y ∈ D.what₂.isot j σ, D.what₂.thetaT D.what₂.mu0 j y = 0 → y = 0 := by
  intro _ _
  unfold _root_.GlobalTheory.LiftRef.ForallRowSideParameters OverRows
  refine GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun K B f T _ w _ Z Wt hX z p0 Y hH _ _ _ _ Rw a M tup Q _ _ j h1 h2 σ y hy h0 => ?_
  obtain ⟨i, rfl⟩ : ∃ i : Fin (w.st Z).toD7.R.m, j = (i : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp only; omega⟩
  exact thetaT_inj_real _ _ _ _ _ _ _ z.R z.F z.cG p0 Y z.pins hH i σ y hy h0
end GlobalTheory.LiftRef.UpInjRows
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaT_mu0_injective_on_isot : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.LiftRef.ForallRowSideParameters hL fun D _ _ _ _ _ => ∀ (j : ℕ) (_ : 1 ≤ j) (_ : j ≤ D.R.m) (σ : D.what₂.FT), ∀ y ∈ D.what₂.isot j σ, D.what₂.thetaT D.what₂.mu0 j y = 0 → y = 0 := by
  first | exact @_root_.GlobalTheory.LiftRef.UpInjRows.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.LiftRef.UpInjRows.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.LiftRef.UpInjRows.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.LiftRefIrr
end GlobalTheory.LiftRefIrr
open GlobalTheory.LiftRefIrr in
theorem GlobalTheory.LiftRef.baseChange_local_at_trivial_character_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.LiftRef.ForallRowSideParameters hL fun D cf _ Rw a M => ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (σ : D.what₂.FT), D.what₂.isot j σ ≠ ⊥ → ∃ (S : Submodule ℂ (Formalism.AUTREP.GAf D.host.E D.R.nV → (M D.what₂.mu0 j h1 h2).wt.W)) (hS : NG.IsIrrRep (M D.what₂.mu0 j h1 h2).wt.ρ S), (NG.isoTyp (M D.what₂.mu0 j h1 h2).wt.ρ S).comap (M D.what₂.mu0 j h1 h2).real ≠ ⊥ ∧ ∀ μ : D.naut.CG 1, (a.chr.e1 μ).1 = cf.mu0 ⟨j - 1, by omega⟩ → ∀ w, IsSplitPl D.host w → D.nbc.locAU j (a.A.cls j h1 h2 (GlobalTheory.LiftRef.autOf (M D.what₂.mu0 j h1 h2) S hS)) w = D.naut.lpChar (D.naut.lpSum (Rw.locR σ w) (spehLoc D.nd D.naut ⟨1, μ, D.R.t⟩ w)) (D.naut.locG D.naut.etaTinv w) := by
  intro hN hL
  have hA := _root_.GlobalTheory.T.thetaT_mu0_injective_on_isot hN hL
  have hB := _root_.GlobalTheory.T.exists_locally_split_lift_alt hN hL
  unfold _root_.GlobalTheory.LiftRef.ForallRowSideParameters at *
  refine GlobalTheory.LiftRef.overRows_and_mono hA hB ?_
  intro K B f T w Z Wt hX z p0 Y hA' hB' Rw a M tup Q hMA hMI j hj1 hj2 σ hσ
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 hσ
  have hθ := fun h => hy0 (hA' Rw a M tup Q hMA hMI j hj1 hj2 σ y hy h)
  obtain ⟨S, hS, F, hF, hne⟩ := exists_irr_pair (M _ j hj1 hj2) _ hθ
  refine ⟨S, hS, ?_, hB' Rw a M tup Q hMA hMI j hj1 hj2 σ S hS ⟨y, hy, F, hF, hne⟩⟩
  intro hb
  rw [hb, Submodule.mem_bot] at hF
  subst hF
  exact hne (inner_zero_left _)
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseChange_localLanglands_at_trivial_twist_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.LiftRef.ForallRowSideParameters hL fun D cf _ Rw a M => ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (σ : D.what₂.FT), D.what₂.isot j σ ≠ ⊥ → ∃ (S : Submodule ℂ (Formalism.AUTREP.GAf D.host.E D.R.nV → (M D.what₂.mu0 j h1 h2).wt.W)) (hS : NG.IsIrrRep (M D.what₂.mu0 j h1 h2).wt.ρ S), (NG.isoTyp (M D.what₂.mu0 j h1 h2).wt.ρ S).comap (M D.what₂.mu0 j h1 h2).real ≠ ⊥ ∧ ∀ μ : D.naut.CG 1, (a.chr.e1 μ).1 = cf.mu0 ⟨j - 1, by omega⟩ → ∀ w, IsSplitPl D.host w → D.nbc.locAU j (a.A.cls j h1 h2 (GlobalTheory.LiftRef.autOf (M D.what₂.mu0 j h1 h2) S hS)) w = D.naut.lpChar (D.naut.lpSum (Rw.locR σ w) (spehLoc D.nd D.naut ⟨1, μ, D.R.t⟩ w)) (D.naut.locG D.naut.etaTinv w) := by
  first | exact @_root_.GlobalTheory.LiftRef.baseChange_local_at_trivial_character_alt | exact _root_.GlobalTheory.LiftRef.baseChange_local_at_trivial_character_alt | (intros; apply _root_.GlobalTheory.LiftRef.baseChange_local_at_trivial_character_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SphericalBaseChangeInertCompatible
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MSphInert
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open GlobalTheory.SphInertRef
noncomputable section
theorem UpperTheory.One.M.sphInert_of_isoTyp_comap_ne_bot : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.LiftRef.ForallRowSideParameters hL fun D _ _ _ a M => ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (S : Submodule ℂ (Formalism.AUTREP.GAf D.host.E D.R.nV → (M D.what₂.mu0 j h1 h2).wt.W)) (hS : NG.IsIrrRep (M D.what₂.mu0 j h1 h2).wt.ρ S), (NG.isoTyp (M D.what₂.mu0 j h1 h2).wt.ρ S).comap (M D.what₂.mu0 j h1 h2).real ≠ ⊥ → SphericalInertData.SphInert D.nd D.naut D.nbc j (a.A.cls j h1 h2 (GlobalTheory.LiftRef.autOf (M D.what₂.mu0 j h1 h2) S hS)) := by
  have hLvl := GlobalTheory.T.standardFrame_nonsplit_maxCompact_in_level
  intro hP hL
  have hG := _root_.UpperTheory.One.M.goodRef_alt hP hL
  unfold _root_.GlobalTheory.LiftRef.ForallRowSideParameters at hG ⊢
  refine GlobalTheory.LiftRef.overRows_and_mono hLvl hG (fun K B f T w Z Wt hX z p0 Y h hg => ?_)
  intro Rw a M tup Q hMA hx j h1 h2 S hS hne w' hw'
  have hgood := hg Rw a M tup Q hMA hx j h1 h2 S hS hne
  obtain ⟨i, rfl⟩ : ∃ i : Fin (w.st Z).toD7.R.m, i.1 + 1 = j := ⟨⟨j - 1, by omega⟩, by simp only; omega⟩
  rw [a.A.sph (i.1 + 1) h1 h2 _ w' (HeightOneSpectrum.under (𝓞 (maximalRealSubfield (w.st Z).toD7.host.E)) w') hw' rfl]
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 hne
  have hry : (M _ _ h1 h2).real y ≠ 0 := fun e =>
    hy0 ((M _ _ h1 h2).real_inj (e.trans (map_zero _).symm))
  obtain ⟨f, hf, hf0, hff⟩ := GlobalTheory.AutUnr.exists_fixed_of_isoTyp _ hS.1.stable
    {κ | κ ∈ Umax (w.st Z).toD7.host.E (w.st Z).toD7.R.nV ∧
      TrivOutside {HeightOneSpectrum.under (𝓞 (maximalRealSubfield (w.st Z).toD7.host.E)) w'} κ} hy hry
    (fun κ hκ => rt_real_eq_of_lev hMA i y κ (h i (hMA.PV i) (hMA.std i) w' hw' κ hκ.1 hκ.2).1
      (h i (hMA.PV i) (hMA.std i) w' hw' κ hκ.1 hκ.2).2)
  exact _root_.UpperTheory.One.M.New.sphMk ⟨f, hf, hf0, fun κ hU htr => hff κ ⟨hU, htr⟩⟩ fun _ => hgood
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.SphInertRef
section Read
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : Formalism.IndefR.Links.RealDat3 D A3 Ks}
  {F : Formalism.IndefR.Links.Face3 D A3} {X0 : BaseLevelRowSide D} {Y : Read R.toRealDat F.lv2 X0} {M : MtFam D}
end Read
end GlobalTheory.SphInertRef
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sph_inert_cls_of_iso_typ_comap_ne_bot : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.LiftRef.ForallRowSideParameters hL fun D _ _ _ a M => ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (S : Submodule ℂ (Formalism.AUTREP.GAf D.host.E D.R.nV → (M D.what₂.mu0 j h1 h2).wt.W)) (hS : NG.IsIrrRep (M D.what₂.mu0 j h1 h2).wt.ρ S), (NG.isoTyp (M D.what₂.mu0 j h1 h2).wt.ρ S).comap (M D.what₂.mu0 j h1 h2).real ≠ ⊥ → SphericalInertData.SphInert D.nd D.naut D.nbc j (a.A.cls j h1 h2 (GlobalTheory.LiftRef.autOf (M D.what₂.mu0 j h1 h2) S hS)) := by
  first | exact @_root_.UpperTheory.One.M.sphInert_of_isoTyp_comap_ne_bot | exact _root_.UpperTheory.One.M.sphInert_of_isoTyp_comap_ne_bot | (intros; apply _root_.UpperTheory.One.M.sphInert_of_isoTyp_comap_ne_bot <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BaseChangeCentralCharacterEqCompNorm
set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
namespace GlobalTheory.LiftChar
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 _root_.Formalism.L2.Host _root_.Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
theorem locComp_of_isRc_classMapD_cenLoc : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.LiftRef.ForallRowSideParameters hL fun D cf _ _ a _ => ∀ j : Fin D.R.m, ∃ μ : D.naut.CG 1, (a.chr.e1 μ).1 = cf.mu0 j ∧ D.naut.csd μ ∧ (∀ w, ¬ IsSplitPl D.host w → D.naut.unr (D.naut.locG μ w) ∧ D.naut.unr (D.naut.locG D.naut.etaTinv w)) ∧ ∀ τ, D.naut.infG D.naut.etaTinv (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) = {-(1 / 2 : ℂ)} ∧ D.naut.infG D.naut.etaTinv (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ) = {(1 / 2 : ℂ)} := by
  intro _ hL
  unfold _root_.GlobalTheory.LiftRef.ForallRowSideParameters OverRows EvLgG
  refine evG_all fun K => lg_all K fun B f T _ => ?_
  intro _ w _ Z Wt hX z p0 Y _ _ _ _ _ Rw a M tup Q _ _
  exact charAt _ _ a.chr
end GlobalTheory.LiftChar
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infG_embTau_eq_neg_half_and_embTauBar_eq_half : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.LiftRef.ForallRowSideParameters hL fun D cf _ _ a _ => ∀ j : Fin D.R.m, ∃ μ : D.naut.CG 1, (a.chr.e1 μ).1 = cf.mu0 j ∧ D.naut.csd μ ∧ (∀ w, ¬ IsSplitPl D.host w → D.naut.unr (D.naut.locG μ w) ∧ D.naut.unr (D.naut.locG D.naut.etaTinv w)) ∧ ∀ τ, D.naut.infG D.naut.etaTinv (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) = {-(1 / 2 : ℂ)} ∧ D.naut.infG D.naut.etaTinv (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ) = {(1 / 2 : ℂ)} := by
  first | exact @_root_.GlobalTheory.LiftChar.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.LiftChar.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.LiftChar.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BaseChangeInfinitesimalCharacter
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltTer
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.LiftInfRef
open Matrix _root_.Formalism.L2.NG GlobalTheory.AlgWtHW NumberField
section Conj
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
end Conj
end GlobalTheory.LiftInfRef
namespace GlobalTheory.LiftInfRef
open Matrix _root_.Formalism.L2.NG GlobalTheory.AlgWtHW NumberField
section Conj2
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
end Conj2
end GlobalTheory.LiftInfRef
namespace GlobalTheory.LiftInfRef
open GlobalTheory.LiftRef
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem core_data_of_point (D : D7) (cf : CharFrame D) (A : _root_.GlobalTheory.HeightCounting.AUSideAlt D) (chr : CharSide D cf) (M : MtFam D)
    {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E} {Q : D.what₂.places.Pl → Finset (PlE D.host)}
    (hIn : MtInput D M tup Q) (k : ℕ) (h1 : 1 ≤ k + 1) (h2 : k + 1 ≤ D.R.m)
    (S : Submodule ℂ (Formalism.AUTREP.GAf D.host.E D.R.nV → (M D.what₂.mu0 (k + 1) h1 h2).wt.W))
    (hS : NG.IsIrrRep (M D.what₂.mu0 (k + 1) h1 h2).wt.ρ S) (μ : D.naut.CG 1)
    (hμ : (chr.e1 μ).1 = cf.mu0 ⟨k, by omega⟩) (τ : D.what₂.Tau) :
    D.nbc.infW (k + 1) (D.nbc.wtAU (k + 1) (A.cls (k + 1) h1 h2 (autOf (M D.what₂.mu0 (k + 1) h1 h2) S hS))) (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) =
        (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.hcSigma (D.hc τ)).map (· - 1 / 2) + isoInf D.nd D.naut [⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩] (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) ∧
      D.nbc.infW (k + 1) (D.nbc.wtAU (k + 1) (A.cls (k + 1) h1 h2 (autOf (M D.what₂.mu0 (k + 1) h1 h2) S hS))) (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ) =
        (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.hcSigma (D.hc τ)).map (fun y => -y + 1 / 2) + isoInf D.nd D.naut [⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩] (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ) := by
  set π := autOf (M D.what₂.mu0 (k + 1) h1 h2) S hS with hπ
  obtain ⟨b, hd, -, -⟩ := GlobalTheory.algWt_contragredient D.host.E D.R.nV π.toAlgWt
  have hw := A.wt (k + 1) h1 h2 π b hd
  obtain ⟨lam, hlam⟩ := (GlobalTheory.T.algWeight_highestWeight_exists_unique_antitone D.host.E D.R.nV b (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ)).1.exists
  obtain ⟨lam', hlam'⟩ := (GlobalTheory.T.algWeight_highestWeight_exists_unique_antitone D.host.E D.R.nV b (ComplexEmbedding.conjugate (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ))).1.exists
  have hbar : GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ = ComplexEmbedding.conjugate (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) := by
    ext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar, ComplexEmbedding.conjugate_coe_eq]
  have hpar : NG.infOf lam = NG.paramV D.R (D.hc τ) ⟨k, by omega⟩ (1 / 2) := hIn.wt D.what₂.mu0 ⟨k, by omega⟩ τ b lam hd hlam
  have hinf1 := A.infW (k + 1) h1 h2 b _ lam hlam
  have hinf2 := A.infW (k + 1) h1 h2 b _ lam' hlam'
  have hconj := infOf_conj hlam hlam'
  have he : (chr.e1 (D.naut.tw μ D.naut.etaTinv)).1 = cf.mu0 ⟨k, by omega⟩ * cf.eta⁻¹ := by
    rw [chr.tw, hμ, chr.etaTinv]
  have hI : (chr.e1 (D.naut.tw μ D.naut.etaTinv)).1.HasInfQ (embPsi D.host)
      (fun g => -eExp D ⟨k, by omega⟩ g - 1 / 2) := by
    rw [he]
    have h1' := (cf.isMu0 ⟨k, by omega⟩).inf
    have h2' : (cf.eta⁻¹).HasInfQ (embPsi D.host) (-(fun _ => 1 / 2)) :=
      GlobalTheory.BlockCharInf.hasInfQ_inv' ⟨fun _ => 1, fun _ => by norm_num, cf.isEta.inf⟩
    convert GlobalTheory.BlockCharInf.hasInfQ_mul' h1' h2' using 1
    ext g
    change -eExp D ⟨k, by omega⟩ g - 1 / 2 = -eExp D ⟨k, by omega⟩ g + -(1 / 2)
    ring
  obtain ⟨hg1, hg2⟩ := chr.infG _ _ hI (D.eTau τ)
  have hval : eExp D ⟨k, by omega⟩ (D.eTau τ) = (D.hc τ).e ⟨k, by omega⟩ := by simp [eExp]
  have hG1 : D.naut.infG (D.naut.tw μ D.naut.etaTinv) (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) = {(-((D.hc τ).e ⟨k, by omega⟩ : ℂ) - 1 / 2)} := by
    rw [show GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ = embPsi D.host (D.eTau τ) from rfl, hg1, hval]; push_cast; ring_nf
  have hG2 : D.naut.infG (D.naut.tw μ D.naut.etaTinv) (ComplexEmbedding.conjugate (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ)) =
      {(((D.hc τ).e ⟨k, by omega⟩ : ℂ) + 1 / 2)} := by
    rw [← hbar, show GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ = (starRingEnd ℂ).comp (embPsi D.host (D.eTau τ)) from rfl, hg2, hval]; push_cast; ring_nf
  rw [hw, hinf1, hbar, hinf2, hconj, hpar]
  constructor
  · unfold isoInf
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hG1, Multiset.map_singleton, bindCast, List.map_map, Function.comp_def, sum_singletons]
    unfold NG.paramV GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.hcSigma
    rw [Multiset.map_add (f := _), Multiset.map_map, Multiset.map_map, ← Multiset.map_coe, Multiset.coe_range]
    refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
    · refine Multiset.map_congr rfl fun i _ => ?_
      simp only [Function.comp_apply]
    · refine Multiset.map_congr rfl fun i _ => ?_
      simp only [Function.comp_apply]
    · refine Multiset.map_congr rfl fun c _ => ?_
      push_cast; ring
  · unfold isoInf
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hG2, Multiset.map_singleton, bindCast, List.map_map, Function.comp_def, sum_singletons]
    unfold NG.paramV GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.hcSigma
    rw [Multiset.map_add (f := _), Multiset.map_add (f := _), Multiset.map_add (f := _), Multiset.map_map, Multiset.map_map, Multiset.map_map,
      Multiset.map_map, Multiset.map_map, ← Multiset.map_coe, Multiset.coe_range]
    refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
    · refine Multiset.map_congr rfl fun i _ => ?_
      simp only [Function.comp_apply]; ring
    · refine Multiset.map_congr rfl fun i _ => ?_
      simp only [Function.comp_apply]; ring
    · have hf := range_rev D.R.t (fun c : ℕ => ((D.hc τ).e ⟨k, by omega⟩ : ℂ) + 1 / 2 - ((D.R.t : ℂ) - 1) / 2 + c)
      refine (Multiset.map_congr rfl fun c _ => ?_).trans (hf.symm.trans (Multiset.map_congr rfl fun c hc => ?_))
      · simp only [Function.comp_apply]; push_cast; ring
      · have hc' := Multiset.mem_range.1 hc
        rw [Nat.cast_sub (show c ≤ D.R.t - 1 by omega), Nat.cast_sub (show 1 ≤ D.R.t by omega)]
        push_cast; ring
end GlobalTheory.LiftInfRef
namespace GlobalTheory.LiftInfRef
end GlobalTheory.LiftInfRef
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.LiftInfRef
open Matrix _root_.Formalism.L2.NG GlobalTheory.AlgWtHW NumberField
section Conj
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
end Conj
end GlobalTheory.LiftInfRef
namespace GlobalTheory.LiftInfRef
open Matrix _root_.Formalism.L2.NG GlobalTheory.AlgWtHW NumberField
section Conj2
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
end Conj2
end GlobalTheory.LiftInfRef
namespace GlobalTheory.LiftInfRef
open GlobalTheory.LiftRef
attribute [local instance] Formalism.BasicNotions.Host.cmStar
end GlobalTheory.LiftInfRef
namespace GlobalTheory.LiftInfRef
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem baseChange_archimedean_compatible_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.LiftRef.ForallRowSideParameters hL fun D cf _ _ a M => ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (S : Submodule ℂ (Formalism.AUTREP.GAf D.host.E D.R.nV → (M D.what₂.mu0 j h1 h2).wt.W)) (hS : NG.IsIrrRep (M D.what₂.mu0 j h1 h2).wt.ρ S) (μ : D.naut.CG 1), (a.chr.e1 μ).1 = cf.mu0 ⟨j - 1, by omega⟩ → ∀ τ, D.nbc.infW j (D.nbc.wtAU j (a.A.cls j h1 h2 (GlobalTheory.LiftRef.autOf (M D.what₂.mu0 j h1 h2) S hS))) (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) = (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.hcSigma (D.hc τ)).map (· - 1 / 2) + isoInf D.nd D.naut [⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩] (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) ∧ D.nbc.infW j (D.nbc.wtAU j (a.A.cls j h1 h2 (GlobalTheory.LiftRef.autOf (M D.what₂.mu0 j h1 h2) S hS))) (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ) = (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.hcSigma (D.hc τ)).map (fun y => -y + 1 / 2) + isoInf D.nd D.naut [⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩] (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ) := by
  intro _ hL
  unfold _root_.GlobalTheory.LiftRef.ForallRowSideParameters OverRows
  refine evLgG_of_forall fun K B f T _ w _ Z Wt hX z p0 Y _ _ _ _ _ => ?_
  intro Rw a M tup Q _ hIn j h1 h2 S hS μ hμ τ
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  exact _root_.GlobalTheory.LiftInfRef.core_data_of_point _ _ a.A a.chr M hIn k h1 h2 S hS μ (by simpa using hμ) τ
end GlobalTheory.LiftInfRef
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseChange_infinitesimalCharacter_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.LiftRef.ForallRowSideParameters hL fun D cf _ _ a M => ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (S : Submodule ℂ (Formalism.AUTREP.GAf D.host.E D.R.nV → (M D.what₂.mu0 j h1 h2).wt.W)) (hS : NG.IsIrrRep (M D.what₂.mu0 j h1 h2).wt.ρ S) (μ : D.naut.CG 1), (a.chr.e1 μ).1 = cf.mu0 ⟨j - 1, by omega⟩ → ∀ τ, D.nbc.infW j (D.nbc.wtAU j (a.A.cls j h1 h2 (GlobalTheory.LiftRef.autOf (M D.what₂.mu0 j h1 h2) S hS))) (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) = (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.hcSigma (D.hc τ)).map (· - 1 / 2) + isoInf D.nd D.naut [⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩] (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) ∧ D.nbc.infW j (D.nbc.wtAU j (a.A.cls j h1 h2 (GlobalTheory.LiftRef.autOf (M D.what₂.mu0 j h1 h2) S hS))) (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ) = (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.hcSigma (D.hc τ)).map (fun y => -y + 1 / 2) + isoInf D.nd D.naut [⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩] (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ) := by
  first | exact @_root_.GlobalTheory.LiftInfRef.baseChange_archimedean_compatible_alt | exact _root_.GlobalTheory.LiftInfRef.baseChange_archimedean_compatible_alt | (intros; apply _root_.GlobalTheory.LiftInfRef.baseChange_archimedean_compatible_alt <;> assumption)
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.LiftRef
theorem baseChange_local_compatible_all_places_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, OverRows fun _ _ _ _ w Z _ _ z _ Y => ∀ Rw, _root_.GlobalTheory.HeightCounting.Up.ParityConditions hL (w.st Z).toD7 (TC.cf w.I w.l Z) (repOf Y) Rw → ∀ (M : MtFam (w.st Z).toD7) tup Q, MtAd Y M → MtInput (w.st Z).toD7 M tup Q → LiftAll (w.st Z).toD7 Rw := by
  intro hP hL
  have h := overRows_and_mono (_root_.GlobalTheory.T.infG_embTau_eq_neg_half_and_embTauBar_eq_half hP hL) (_root_.GlobalTheory.T.baseChange_localLanglands_at_trivial_twist_alt hP hL) (fun _ _ _ _ _ _ _ _ _ _ _ a b => And.intro a b)
  have h' := overRows_and_mono h (_root_.GlobalTheory.T.sph_inert_cls_of_iso_typ_comap_ne_bot hP hL) (fun _ _ _ _ _ _ _ _ _ _ _ a b => And.intro a b)
  refine overRows_and_mono h' (_root_.GlobalTheory.T.baseChange_infinitesimalCharacter_alt hP hL) ?_
  rintro K B f T w Z Wt hX z p0 Y ⟨⟨hc, hl⟩, hs⟩ hi Rw a M tup Q hA hI j h1 h2 σ hσ
  obtain ⟨S, hS, hm, hloc⟩ := hl Rw a M tup Q hA hI j h1 h2 σ hσ
  obtain ⟨μ, hμ, hcsd, hunr, heta⟩ := hc Rw a M tup Q hA hI ⟨j - 1, by omega⟩
  exact ⟨_, μ, ⟨hcsd, hunr, hs Rw a M tup Q hA hI j h1 h2 S hS hm, hloc μ hμ, heta, hi Rw a M tup Q hA hI j h1 h2 S hS μ hμ⟩⟩
end GlobalTheory.LiftRef
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftAll_of_parIn_of_mtInput : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, OverRows fun _ _ _ _ w Z _ _ z _ Y => ∀ Rw, _root_.GlobalTheory.HeightCounting.Up.ParityConditions hL (w.st Z).toD7 (TC.cf w.I w.l Z) (repOf Y) Rw → ∀ (M : MtFam (w.st Z).toD7) tup Q, MtAd Y M → MtInput (w.st Z).toD7 M tup Q → LiftAll (w.st Z).toD7 Rw := by
  first | exact @_root_.GlobalTheory.LiftRef.baseChange_local_compatible_all_places_alt | exact _root_.GlobalTheory.LiftRef.baseChange_local_compatible_all_places_alt | (intros; apply _root_.GlobalTheory.LiftRef.baseChange_local_compatible_all_places_alt <;> assumption)
end
end
