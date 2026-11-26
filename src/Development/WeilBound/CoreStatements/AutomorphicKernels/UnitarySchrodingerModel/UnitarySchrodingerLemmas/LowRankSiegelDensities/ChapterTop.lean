module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.LowRankSiegelDensities.MassTop
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.OneVecBinary
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.UnramifiedSchwartzDensity.SchTop

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.LowRankSiegelDensities.ChapterA
theorem PositivityTheory.PfSWUS.HMass.siegelDensitiesLowA_of_sch (hB : PositivityTheory.PfSWUS.HMass.SchwartzDensInf) :
    PositivityTheory.PfSWUS.HMass.SiegelDensitiesLowA :=
  PositivityTheory.PfSWUS.HMass.siegelDensitiesLowA_of_leaves PositivityTheory.Rg.Mass.oneVecBinary hB
end

theorem PositivityTheory.PfSWUS.HMass.siegelDensitiesLowA : PositivityTheory.PfSWUS.HMass.SiegelDensitiesLowA :=
  PositivityTheory.PfSWUS.HMass.siegelDensitiesLowA_of_sch PositivityTheory.PfSWUS.SchInf.schwartzDensInf
