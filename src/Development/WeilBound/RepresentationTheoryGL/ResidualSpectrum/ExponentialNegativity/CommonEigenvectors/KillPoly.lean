module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PolynomialKilling.KillPoly4

@[expose] public section

noncomputable section

open Polynomial

namespace PositivityTheory.Rg.Rs.JKillPoly

end JKillPoly

open JKillPoly in
theorem killPoly_holds : KillPoly := KillingPolynomialDegreeFour.killPoly4

end PositivityTheory.Rg.Rs

end
