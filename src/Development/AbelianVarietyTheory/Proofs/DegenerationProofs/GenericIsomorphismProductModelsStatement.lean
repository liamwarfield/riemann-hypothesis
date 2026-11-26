module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericIsomorphismProductModels
public meta import Lean.Elab.Command

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

-- c189: restore Model.prod for incomplete imports.
run_cmd
  unless (← Lean.getEnv).contains `GlobalTheory.SS.Model.prod do
    let prodName := Lean.mkIdent `_root_.GlobalTheory.SS.Model.prod
    Lean.Elab.Command.elabCommand (← `(
      private noncomputable def $prodName:ident
          {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K]
          {A A' : Over (Sp K)} (M : GlobalTheory.SS.Model R A)
          (N : GlobalTheory.SS.Model R A') : GlobalTheory.SS.Model R (A ⊗ A') where
        Y := M.Y ⊗ N.Y
        e := (Functor.Monoidal.μIso (Over.pullback (spMap (algebraMap R K))) M.Y N.Y).symm ≪≫
          tensorIso M.e N.e
        smooth := by
          have := M.smooth
          have := N.smooth
          show Smooth (pullback.fst _ _ ≫ M.Y.hom)
          infer_instance
        sep := by
          have := M.sep
          have := N.sep
          show IsSeparated (pullback.fst _ _ ≫ M.Y.hom)
          infer_instance
        qc := by
          have := M.qc
          have := N.qc
          show QuasiCompact (pullback.fst _ _ ≫ M.Y.hom)
          infer_instance))

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_isomorphism_product_models : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A A' B B' : Over (Sp K)) [IsIntegral A.left] [IsIntegral (A ⊗ B).left] (M : Model R A) (M' : Model R A') (N : Model R B) (N' : Model R B') (f : A ≅ A') (Θ : A ⊗ B ⟶ A' ⊗ B'), M.Irr → M'.Irr → N.Irr → N'.Irr → Θ ≫ fst A' B' = fst A B ≫ f.hom → GenIso (M.prod N) (M'.prod N') Θ → GenIso M M' f.hom := by
  first | exact @GlobalTheory.SS.GenProj.genIso_of_prod | exact GlobalTheory.SS.GenProj.genIso_of_prod | (intros; apply GlobalTheory.SS.GenProj.genIso_of_prod <;> assumption)
