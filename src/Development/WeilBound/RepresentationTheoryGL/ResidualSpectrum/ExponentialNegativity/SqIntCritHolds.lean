module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.SqIntCritOf
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.UniformInitialGrowth.InitBnd
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.BoxVolumes.ExistsMeasureLeProd
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.DiagonalInfinityValues.InfGLValDiag

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.SqIntCritOfFinTr
namespace PositivityTheory.Rg.Rs

theorem sqIntCrit_of_finTr (h : FinTr) : SqIntCrit := sqIntCrit_of initBnd_holds h boxvol_holds

end PositivityTheory.Rg.Rs
end

namespace PositivityTheory.Rg.Rs

theorem sqIntCrit_holds : SqIntCrit := sqIntCrit_of_finTr finTr_holds

end PositivityTheory.Rg.Rs
