module

public import Formalism.SharpRestriction.InertJacobiLevels.ExistsLarge
public import Formalism.SharpRestriction.InertJacobiLevels.TiesView
public import Formalism.SharpRestriction.InertJacobiLevels.ExtraGatC

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits NumberField

abbrev Core : Type 1 := Σ R : Ranks, Host R × (↥(R.Psi) → HCParam R)

end Formalism.MainNotions.Inhab

end
