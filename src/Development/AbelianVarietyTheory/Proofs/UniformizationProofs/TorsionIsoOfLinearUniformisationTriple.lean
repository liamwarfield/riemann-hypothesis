module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FunctorialOfUnif
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemistableReductionPpavPadicField

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionIsoOfLinearUniformisationTriple
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionIsoOfLinearUniformisationTriple
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
namespace GlobalTheory.UT

theorem torsionIso_of_pelUnif : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (t : SAB H (Sp R)) (P : PELUnif I t), P.TorsionIso := by
  intro hL h1 h2 h3 h4 E _ _ _ H R _ _ _ I hI t P F _ _ _ k hk
  letI := H.starRing
  obtain ⟨f, hf⟩ := GlobalTheory.T.uniformisation_torsion_identification_with_pairing hL R I hI P.D P.A t.G t.semi P.U F k hk
  have hadj : ∀ a : NumberField.RingOfIntegers E,
      LBIso (cubeLB t.G ![fst t.G t.G ≫ t.act.toRingAct.act a, snd t.G t.G] P.U.LG.L)
        (cubeLB t.G ![fst t.G t.G, snd t.G t.G ≫ t.act.toRingAct.act (star a)] P.U.LG.L) := by
    intro a
    rw [P.bundle]
    exact t.adj a
  have hlin := GlobalTheory.T.linear_uniformisation_torsion_map_isLinear hL h1 h2 h3 h4 R I hI P.D P.A t.G t.semi P.U F
    (NumberField.RingOfIntegers E) P.oD P.oA t.act.toRingAct P.lin hadj k hk f hf
  exact ⟨f, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hlin, hf.2.2.2.2⟩
end GlobalTheory.UT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionIsoOfLinearUniformisationTripleStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionIso_of_linear_uniformisation_triple : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (t : SAB H (Sp R)) (P : PELUnif I t), P.TorsionIso := by
  first | exact @GlobalTheory.UT.torsionIso_of_pelUnif | exact GlobalTheory.UT.torsionIso_of_pelUnif | (intros; apply GlobalTheory.UT.torsionIso_of_pelUnif <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperOfSubsingleton
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TateUnif

theorem rank_add_dim {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} (hR : AdmBase R I) {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (hG : IsSemiAbelian G) (U : Unif I D A G) :
    Module.finrank ℤ D.toPre.X + D.toPre.P.g = A.g := by
  obtain ⟨hL, hL₂, -⟩ := GlobalTheory.allSixLaws
  have := hG.geomConnected
  have h₁ := GlobalTheory.finrank_fam_of_expBij hL.secBaseChange R I hR D A G U.toUnifPre 2 one_le_two
    (U.expand 2 one_le_two)
  have h₂ := (GlobalTheory.FamDimension.main hL.globalFns hL.cube hL.square hL₂.secTwist R I D (FractionRing R) 2
    one_le_two).2
  exact Nat.pow_right_injective le_rfl (h₂.symm.trans h₁)

end GlobalTheory.TateUnif
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTotalClosed
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

namespace GlobalTheory

theorem uniformisation_total_closed : USt :=
  GlobalTheory.T.uniformisation_complete_dvr_of_laws GlobalTheory.T.all_six_abelian_scheme_laws_hold.1 GlobalTheory.T.all_six_abelian_scheme_laws_hold.2.1 GlobalTheory.T.all_six_abelian_scheme_laws_hold.2.2.1 GlobalTheory.T.all_six_abelian_scheme_laws_hold.2.2.2.1
    GlobalTheory.T.all_six_abelian_scheme_laws_hold.2.2.2.2.1

end GlobalTheory
end
