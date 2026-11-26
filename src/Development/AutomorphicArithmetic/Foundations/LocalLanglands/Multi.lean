module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.Outright
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalLanglandsExistence.LanglandsDataDualGLOfCosocle
public import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.GrothendieckRingPolynomialOfSeg
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.PublishedTheoremStatements.ProvedMore
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.PublishedTheoremStatements.BridgesMore

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.EssSquareIntegrableSegmentsHolds
namespace PositivityTheory.Groth

theorem grothendieckRingPolynomial_holds : GlobalTheory.Published.GrothendieckRingPolynomial :=
  grothendieckRingPolynomial_of_seg PositivityTheory.RgGu.segmentRepresentation

end PositivityTheory.Groth
end

namespace UpperTheory.Zero.LLC.Pr

theorem exh : GlobalTheory.Published.LanglandsExhaustionGL := PositivityTheory.Exh.langlandsExhaustionGL_holds
theorem multi : GlobalTheory.Published.LanglandsMultisegments := PositivityTheory.Exh.langlandsMultisegments_holds
theorem cos : GlobalTheory.Published.StandardCosocleGL := PositivityTheory.Exh.standardCosocleGL_holds
theorem bz : GlobalTheory.Published.BernsteinZelevinskyFiniteness := PositivityTheory.Prw.bernsteinZelevinskyFiniteness_holds
theorem zel : GlobalTheory.Published.ZelevinskyPolynomialRing :=
  PositivityTheory.Prw.zelevinskyPolynomialRing_of bz PositivityTheory.RgGu.segmentRepresentation PositivityTheory.Groth.grothendieckRingPolynomial_holds
theorem dual : GlobalTheory.Published.LanglandsDataDualGL := PositivityTheory.Pf1.LocalLanglands.LDual.langlandsDataDualGL_of_cosocle cos
theorem adm : GlobalTheory.Published.IrreducibleAdmissibleGL := PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
theorem dzs : GlobalTheory.Published.DepthZeroSupport := GlobalTheory.SmGL.depthZeroSupport

end UpperTheory.Zero.LLC.Pr
