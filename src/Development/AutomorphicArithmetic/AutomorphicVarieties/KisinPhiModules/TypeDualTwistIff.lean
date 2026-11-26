module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KisinCrystalline.TypeSt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsInertiaInfiniteCyclotomic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc UpperTheory.V.Loc UpperTheory.V.Lit

section
open TensorProduct GlobalTheory.Pst Polynomial Matrix

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} {B : Type} [CommRing B] [Algebra ℚ_[l] B]

end
