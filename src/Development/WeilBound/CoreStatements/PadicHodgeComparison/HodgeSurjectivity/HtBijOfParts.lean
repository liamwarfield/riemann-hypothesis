module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.TowerRallisLemma

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.OntoAllOf
namespace CrystallineSemistableComparison.Onto

structure Parts : Prop where
  mv : MVBij
  surj : OneSurj
  cov : CovDesc
  site : SiteLaws
  on : OnIso
  zar : ZarAbs
  aff : AffOm
  nat : OmNat
  laws : FormLaws
  dw : DWedge
  dl : DLog
  kun : OmKun
  fc : FormCup
  c1 : FirstChernCoboundary
  div : DivCover
  chart : ChartLaws
  bij : ChartBij
  iso : IsoBij
  cup : CupLaws
  zarRel : ZarRelOf
  affRel : AffRelOf
  lift : RelLiftOf
  inj : RelInjOf
  cone : ConeKillOf
  kill : RelKillOf
  kunAff : KunAffOf
  slant : SlantOf
  killOf : KillOf3
  onto : OntoOf3
  low : OntoLow
  retr : Retract

theorem Parts.hodgeKill (h : Parts) : HodgeKill :=
  have zr := h.zarRel h.site h.on h.zar
  h.killOf h.site h.cup (h.lift h.site h.on) (h.inj h.site h.mv h.cov zr h.chart h.bij h.iso)
    (h.kill h.site h.cov zr h.aff h.nat (h.affRel h.site h.on h.aff h.nat h.laws) h.laws h.dw h.dl h.fc h.c1 h.div (h.cone h.surj))

theorem Parts.slant' (h : Parts) : Slant :=
  h.slant h.site h.mv h.cov h.zar h.aff (h.kunAff h.site h.aff h.nat h.laws h.fc h.kun)

theorem ontoAll_of (h : Parts) (hS : SqEx3) (hD : DiagEt3) (hF : EtFin) : OntoAll :=
  h.low h.cup h.retr (h.onto h.cup h.slant' h.hodgeKill hS hD hF)

end CrystallineSemistableComparison.Onto
end

noncomputable section

open AlgebraicGeometry

namespace CrystallineSemistableComparison.Onto

open HT

def HTBij : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K],
    ∃ P : HTPre l K, ∀ M : Model l K, M.Sm → (∀ n, P.Inj M n) ∧ (∀ d, M.Conn d → P.Top M d) ∧
      ∀ d, SmoothOfRelativeDimension d M.p → ∀ n, Surj P M n ∧
        Module.finrank ℚ_[l] (M.V n) = ∑ a ∈ Finset.range (n + 1), Module.finrank K (Hdg M.q a n)

theorem htBij_of_parts (h : Parts) (hR : HodgeTateDimensionEquality) (hH : HodgeTateMapExists) (hS : SqEx3) (hD : DiagEt3) (hF : EtFin) : HTBij := by
  intro l _ K _
  obtain ⟨P, hP⟩ := hH l K
  refine ⟨P, fun M hM => ⟨(hP M hM).1, (hP M hM).2, fun d hd n => ?_⟩⟩
  have hs : Surj P M n := ontoAll_of h hS hD hF l K P (fun N hN => (hP N hN).1) M d hM hd n
  exact ⟨hs, hR l K P M n hM (hF l K M hM n) ((hP M hM).1 n) hs⟩

end CrystallineSemistableComparison.Onto

end
