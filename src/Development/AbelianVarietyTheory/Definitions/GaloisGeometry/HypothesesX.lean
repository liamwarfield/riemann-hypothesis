module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HtCard
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFactorisationCuspidal
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger

@[expose] public section

namespace GlobalTheory.NRows

structure HypothesesX : Prop where
  weil : GlobalTheory.Published.WeilRepresentationUnitaryPair
  ds : GlobalTheory.Published.DiscreteSeriesExists
  ana : GlobalTheory.Published.HarishChandraAnalyticity
  dsc : GlobalTheory.Published.DiscreteSeriesClassification
  trc : GlobalTheory.Published.CuspTraceClass
  dm : GlobalTheory.Published.DixmierMalliavinFactorisation
  flath : GlobalTheory.Published.FlathFactorisation
  pc : GlobalTheory.Published.PseudoCoefficientUpq
  hcc : GlobalTheory.Published.HarishChandraCharacters
  lc : GlobalTheory.Published.LanglandsClassification
  lw : GlobalTheory.Published.LabesseWaldspurger
  sw : GlobalTheory.Published.WeilSiegelFormulaUnitary
  ft : GlobalTheory.Published.RegularisedSiegelWeilFirstTerm
  dbl : GlobalTheory.Published.DoublingMethod
  udbl : GlobalTheory.Published.UnramifiedDoublingGL
  hl : GlobalTheory.Published.HeckeLPartialContinuation
  ht : GlobalTheory.HeightCounting.HtCard

end GlobalTheory.NRows
