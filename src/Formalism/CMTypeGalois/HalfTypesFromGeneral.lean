module

public import Formalism.CMTypeGalois.CMTypeFrobenius.MQGalois

@[expose] public section

open NumberField Ideal

namespace Formalism.Q3

theorem mqKummer : MQKummer := mqKummer_of mqGalois

end Formalism.Q3
