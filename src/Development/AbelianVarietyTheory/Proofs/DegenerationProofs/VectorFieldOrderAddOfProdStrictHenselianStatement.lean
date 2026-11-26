module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.VectorFieldOrderAddOfProdStrictHenselian
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
theorem _root_.GlobalTheory.T.vectorFieldOrder_add_of_prod_strictHenselian : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (π : R), Irreducible π → ∀ (A A' : Over (Sp K)) (I I' : Type) [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I'] (D : I → VF A) (D' : I' → VF A'), IsFrame D → IsFrame D' → ∃ D₂ : I ⊕ I' → VF (A ⊗ A'), IsFrame D₂ ∧ ∀ (M : Model R A) (N : Model R A') (m n : ℤ), M.Irr → N.Irr → HasOrd M D π m → HasOrd N D' π n → HasOrd (M.prod N) D₂ π (m + n) := by
  first | exact @GlobalTheory.SS.OrdProd.ord_prod | exact GlobalTheory.SS.OrdProd.ord_prod | (intros; apply GlobalTheory.SS.OrdProd.ord_prod <;> assumption)
