module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.BlockTheory.AbelianSchemeLaw.HomExtendsOverDVR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace GlobalTheory.IndefiniteRowSideFullHecke.HomExtensionOverDVR

noncomputable abbrev genericPt (T K : Type) [CommRing T] [Field K] [Algebra T K] :
    Spec (.of K) ⟶ Spec (.of T) :=
  Spec.map (CommRingCat.ofHom (algebraMap T K))

def HomExtendsOverDVR : Prop :=
  ∀ (T : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    (K : Type) [Field K] [Algebra T K] [IsFractionRing T K]
    (G G' : Over (Spec (.of T))) [GrpObj G] [GrpObj G'],
    ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G → ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G' →
    ∀ f : (Over.pullback (genericPt T K)).obj G ⟶ (Over.pullback (genericPt T K)).obj G',
      IsMonHom f →
      ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (genericPt T K)).map F = f

end GlobalTheory.IndefiniteRowSideFullHecke.HomExtensionOverDVR
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.HomExtExamples

theorem homExtendsOverDVR_holds : GlobalTheory.IndefiniteRowSideFullHecke.HomExtensionOverDVR.HomExtendsOverDVR :=
  fun T _ _ _ K _ _ _ G G' _ _ => GlobalTheory.semiAbelian_hom_extends_uniquely_dvr T K G G'

theorem homExtendsOverDVR_iff : GlobalTheory.IndefiniteRowSideFullHecke.HomExtensionOverDVR.HomExtendsOverDVR ↔ GlobalTheory.LN.HomExtSt :=
  ⟨fun h T K _ _ _ _ _ _ => h T K, fun h T _ _ _ K => h T K⟩

theorem homExtSt_holds : GlobalTheory.LN.HomExtSt := homExtendsOverDVR_iff.1 homExtendsOverDVR_holds

end GlobalTheory.HomExtExamples
