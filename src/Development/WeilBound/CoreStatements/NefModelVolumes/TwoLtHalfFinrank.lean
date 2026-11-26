module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightAbsEntrySumNonneg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumAbsExOfLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageHeightAddLogNonneg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordTensorDataFactorInclusionProjectionProps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFactorExistsUniqueConstMulIntegralGenerat

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

namespace GlobalTheory.CovHt.HtTopG

theorem two_lt_half_finrank (D : D7) : 2 < Module.finrank ℚ D.host.E / 2 := by
  have := D.eight_le_f
  rw [D.host.finrank_cmField]
  unfold Ranks.f Ranks.n at *
  omega

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} {p : PtAt ex Csz} {i : Fin D.R.m} {Y : Cov p i}

end Point

end GlobalTheory.CovHt.HtTopG

end
