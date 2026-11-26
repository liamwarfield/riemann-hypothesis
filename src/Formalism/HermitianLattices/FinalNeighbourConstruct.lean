module

public import Formalism.LatticeTheta.ThetaShiftInversion
public import Formalism.HermitianLattices.HermitianLatticesProofs.IndexBasic
public import Formalism.HermitianLattices.HermitianLatticesProofs.TraceReal
public import Formalism.HermitianLattices.HermitianLatticesProofs.ClassSetAssembly
public import Formalism.HermitianLattices.HermitianLatticesProofs.MajDual
public import Formalism.HermitianLattices.HermitianLatticesProofs.GenusCovol
public import Formalism.HermitianLattices.StatementMass
public import Formalism.HermitianLattices.HermitianLatticesProofs.UnimodUnramUnique

@[expose] public section

section -- merged from Formalism.HermitianLattices.HermitianLatticesProofs.ClassSetFinite
namespace Formalism.HermitianLatticesTheory

theorem classSetFinite : ClassSetFinite :=
  classSetFinite_of traceReal genusCovolBound shortVectors genusScale finIntermediate isomOfTrace

end Formalism.HermitianLatticesTheory
end

namespace Formalism.HermitianLatticesTheory

theorem final_isomAct : IsomAct := Formalism.HermitianLatticesTheory.isomAct
theorem final_genusBasic : GenusBasic := Formalism.HermitianLatticesTheory.genusBasic
theorem final_finIntermediate : FinIntermediate := Formalism.HermitianLatticesTheory.finIntermediate
theorem final_shortVectors : ShortVectors := Formalism.HermitianLatticesTheory.shortVectors
theorem final_isomOfTrace : IsomOfTrace := Formalism.HermitianLatticesTheory.isomOfTrace
theorem final_traceReal : TraceReal := Formalism.HermitianLatticesTheory.traceReal
theorem final_autFinite : AutFinite := Formalism.HermitianLatticesTheory.autFinite
theorem final_genusCovol : GenusCovol := Formalism.HermitianLatticesTheory.genusCovol
theorem final_classSetFinite : ClassSetFinite := Formalism.HermitianLatticesTheory.classSetFinite

end Formalism.HermitianLatticesTheory
