module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ProdIrrAndWeakNeron
public meta import Lean.Elab.Command

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

-- c189: restore Model.prod for incomplete imports.
open CategoryTheory Limits MonoidalCategory AlgebraicGeometry in
open ReciprocityTheory.ChartRestriction.G.Geo.Tor in
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
theorem _root_.GlobalTheory.T.prod_irr_and_weakNeron' : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A A' : Over (Sp K)), (∀ (M : Model R A) (N : Model R A'), M.Irr → N.Irr → (M.prod N).Irr) ∧ ∀ (I I' : Type) (M : I → Model R A) (N : I' → Model R A'), WeakNeron M → WeakNeron N → WeakNeron (fun p : I × I' => (M p.1).prod (N p.2)) := by
  first | exact @GlobalTheory.SS.prod_irr_and_weakNeron | exact GlobalTheory.SS.prod_irr_and_weakNeron | (intros; apply GlobalTheory.SS.prod_irr_and_weakNeron <;> assumption)
