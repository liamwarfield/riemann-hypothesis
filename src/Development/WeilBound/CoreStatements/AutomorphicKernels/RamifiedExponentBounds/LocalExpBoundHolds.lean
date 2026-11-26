module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.TemperedEigenvalueNorms.AddOneLeOfPrecedes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenericUnitaryDualGl
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.BernsteinExponentBounds.ExpBound
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.GenericUnitary.IsGenericOfEquiv
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnitaryDualGLOfTwo

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.RamifiedExponentBounds.LocalSpreadOfLocalExpBound
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace PositivityTheory.JsR

def LocalExpBound : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V),
    IsSmooth π → π.IsIrreducible → IsUnitarisable π → IsGeneric π →
    ∃ (h : ℕ) (δ : Fin h → IrrGL (k := k)) (Δ : Fin h → Segment k) (s : Fin h → ℝ),
      (∀ j, IsLSeg (Δ j) (δ j).rep) ∧ (∀ j, PositivityTheory.UdReth2.IsCentred (Δ j)) ∧ (∀ j, |s j| < 1 / 2) ∧
      ∃ hd : ∑ j, ((δ j).nu (s j)).1 = N, Nonempty (π.Equiv (prodIrr (fun j => (δ j).nu (s j)) hd))

end PositivityTheory.JsR

end
end

namespace PositivityTheory.JsR

theorem localExpBound_holds : LocalExpBound := by
  intro k _ _ _ _ _ N V _ _ π hs hi hu hg
  obtain ⟨h, δ, Δ, s, hΔ, hc, hb, hd⟩ := PositivityTheory.RgUd.Exp.genUnitCCOf PositivityTheory.RgUd.expBound GlobalTheory.RgGu.Holds.genericUnlinkedGL_holds
    k N V π hs hi hu hg
  exact ⟨h, δ, Δ, s, hΔ, fun j _ hω z => PositivityTheory.RgUd.UOrder.log_norm_centralChar_u (hΔ j) (hc j) hω z, hb, hd⟩

end PositivityTheory.JsR
