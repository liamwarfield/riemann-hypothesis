module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CInfGood
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulEllTheta
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsOfH0EqOneClosedFields
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertUnifTangentWeilPairing
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianVarietyTorsionCardEqPowProof
public import Development.AbelianVarietyTheory.Counterexamples.AbelianLawCounterexamples.WeilIsUniqueOfLocal

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GeoRead
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Plug

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar.Rec

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {RM : Top.RootModel (CMType H) (Dw.p + Dw.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))} {Fx : FixedData Y Sys}
  {Or : RootOrigin Y S RM Fx} {Fr : Small.GenFrame Or} {h : GenFrEx Xo c} {Z : Comp Xo c}

def GeoRead (Rd : Reading Fr h Z) : Prop :=
  letI := Small.cstAlg Or
  ∃ y' : FrPt Xo c RM.Ω, FrMap ({ Rd.φ with commutes' := Rd.φ_cst } : Om Z →ₐ[c.F] RM.Ω) (genFr h Z) y' ∧
    FrBor Rd.t y' Fr.y₀

end GlobalTheory.CompanionTheory.Ar.Plug
end
end

section -- merged from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsOfPolAV
section -- merged from Development.AbelianVarietyTheory.Counterexamples.AbelianLawCounterexamples.ExistsTwoTorsionWeilDegenerate
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PairingLawZeroCounterexample

open GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw

theorem laws : WeilSt ∧ WeilNondegSt ∧ CharPairSt :=
  have h := GlobalTheory.AbLaw.FromCube.all_of_cubeGen GlobalTheory.AbLaw.CubeAssembly.cube_and_sections.1
  ⟨h.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1⟩

theorem lifts : ∀ (S : Scheme.{0}) (P : PolAV S) (N : ℕ) (T : Over S) (x : T ⟶ P.A), x ^ N = 1 →
    ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∃ θ : ThetaGrp P.A P.L N (overRes V), θ.pt = overResι V ≫ x :=
  (GlobalTheory.kerPow_of_square (GlobalTheory.AbSquare.square_of_cube GlobalTheory.AbLaw.CubeAssembly.cube_and_sections.1).1).2.2

end GlobalTheory.PairingLawZeroCounterexample
end
end

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GenWeilModel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

def ext {ξ : Spec (CommRingCat.of Ω) ⟶ X} {k : Type} [Field k] (i : Ω →+* k) :
    Over.mk (spMap i ≫ ξ) ⟶ Over.mk ξ := Over.homMk (spMap i) rfl

theorem unitOn_ext {k : Type} [Field k] (i : Ω →+* k) (u : Ωˣ) :
    Units.map (spMap i).appTop.hom.toMonoidHom (unitOn u) = unitOn (Units.map i.toMonoidHom u) := by
  ext
  exact congrArg (fun f => f.hom (u : Ω)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom i)).symm

theorem unitOn_bij {R : Type} [CommRing R] : Function.Bijective (unitOn (R := R)) :=
  (Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm.toMulEquiv).bijective

theorem unitOn_one {R : Type} [CommRing R] : unitOn (1 : Rˣ) = 1 := map_one _

end GlobalTheory.CompanionTheory.Ar.GenWeilModel
end
end
