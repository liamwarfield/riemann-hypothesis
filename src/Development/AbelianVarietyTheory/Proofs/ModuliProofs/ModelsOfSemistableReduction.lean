module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliSchemeLevelMapsHeckePoints
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFullLevelAmpleModelOfSemistableReduction
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LocalModelSystemTransitionSiegelClauses
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliSchemeLevelMapsHeckePointsStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalModelSystemsAmpleFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalModelSystemsAmpleFrames
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.Models

theorem exists_localSystems_ample :
    GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → Out.Laws3 → TopAmpExists → N1 → GlobalTheory.LN.ModelsSt := by
  intro hext hL hL2 hL3 htop hN1 E _ _ _ H D hpq Xo
  obtain ⟨-, hN⟩ := hN1
  have hlev : ToroidalLevelCompatibility (H := H) (D := D) := (hN E H D hpq).1

  obtain ⟨S, hS⟩ := GlobalTheory.T.exists_localModelSystem_ampleFrames_fullLevel hext hL hL2 hL3 htop E H D Xo hpq hlev
  refine ⟨S.Y, fun p W hp hW => ⟨GlobalTheory.T.localModelSystem_transition_siegel_clauses hext hL hL2 hL3 E H D Xo hpq hlev S p W hp hW, fun i => ?_⟩,
    GlobalTheory.T.exists_global_model_of_local_models hext hL hL2 hL3 E H D Xo hpq hlev S⟩
  refine ⟨(GlobalTheory.T.localModel_oneModel_and_splitFibres hext hL hL2 hL3 E H D Xo hpq hlev S p W hp hW i).2, ?_⟩

  obtain ⟨l₀, h₀, hr⟩ := S.raises p W hp hW i
  obtain ⟨k, hk⟩ := hS (S.ch p)
  have hc := (GlobalTheory.CoeffRings.coeff_isDedFrac E H i.l i.c).2.2.2 p W hp hW
  have hcop : (S.n (S.ch p)).Coprime p := (Nat.coprime_primes (S.aux _).1 hp).2 (S.ch_ne p)
  exact GlobalTheory.T.raised_model_finite_cover_ample_frames hL hL2 hL3 E H D Xo (S.n (S.ch p)) (S.n (S.ch p) ^ S.J (S.ch p)) k (S.T (S.ch p)) hlev
    l₀ i.l (S.B (S.ch p) l₀ h₀.1) i.c _ (i.c.V W).subtype (S.Y p W hp hW i) (S.aux _).1 (S.aux _).2.1
    ⟨_, rfl⟩ (hc.2.1 _ hcop) ((GlobalTheory.Models.primeToPart_spec E H p hp).2.1 i.l l₀ h₀).1 hc.1 hr hk

end GlobalTheory.Models
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalModelSystemsAmpleFramesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localModelSystems_ampleFrames : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → Out.Laws3 → TopAmpExists → N1 → GlobalTheory.LN.ModelsSt := by
  first | exact @GlobalTheory.Models.exists_localSystems_ample | exact GlobalTheory.Models.exists_localSystems_ample | (intros; apply GlobalTheory.Models.exists_localSystems_ample <;> assumption)
end
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem modelsSt_of_semistableReduction : GlobalTheory.Published.SemistableReductionSt → GlobalTheory.LN.ModelsSt :=
  fun S => GlobalTheory.T.exists_localModelSystems_ampleFrames GlobalTheory.homExtension_semiAbelian_dvr GlobalTheory.T.all_six_abelian_scheme_laws_hold.1 GlobalTheory.T.all_six_abelian_scheme_laws_hold.2.1
    GlobalTheory.T.all_six_abelian_scheme_laws_hold.2.2.1 (GlobalTheory.T.exists_fullLevelAmpleModel_of_semistableReduction S) GlobalTheory.T.moduliScheme_levelMaps_heckePoints'

end GlobalTheory
