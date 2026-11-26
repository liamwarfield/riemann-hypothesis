module

public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.NarrowCondition
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.AscSeedHolds2

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.DiscreteSpectrumUnitarity.UsedAsc
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Rs

namespace Re.Asc

theorem hasSpehComp (h3 : Clause3Asc) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
    {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N a d : ℕ} (hN : 1 ≤ N)
    {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) {π : CuspSub E a} (hn : IsNormalised π) (e : AscEmb V π d) :
    HasSpehComp V π d := by
  refine ⟨fun w => ?_, h3 E N a d V π hN hV (GlobalTheory.SpehPair.isUnitary_of_isNormalised hn) hn e, fun τ => ?_⟩
  · obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF E a π w
    obtain ⟨σ', hσ'⟩ := GlobalTheory.DiscLocEx.exists_isLocCompGL hF E N V hV w
    exact ⟨σ, σ', hσ, hσ'⟩
  · obtain ⟨m', hm'⟩ := PInfInd2A.exists_hasInfCharGL hV τ
    obtain ⟨m₀, hm₀, rfl⟩ := infAsc_holds E N a d V π hV e τ m' hm'
    refine ⟨m₀, hm₀, ?_⟩
    have e' : (∑ i : Fin d, m₀.map (· + (spehExp d i : ℂ))) = GlobalTheory.SphGal.spehInf d m₀ := by
      simp only [GlobalTheory.SphGal.spehInf, spehExp]
      push_cast
      rfl
    rw [← e']
    exact hm'

section Pair

end Pair

section Local

open GlobalTheory.DefiniteBC GlobalTheory.BcSpeh GlobalTheory.BcSpehProof

end Local

end Re.Asc

end PositivityTheory.Rg.Rs

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.NarrowAsc
open PositivityTheory.Rg.Rs in
theorem UpperTheory.BaseChangeIdentities.ascComp : UpperTheory.BaseChangeIdentities.AscComp := by
  intro E _ _ _ N hN
  refine ⟨fun a π ha hn => ?_, fun V hV a d π hn e =>
    Re.Asc.hasSpehComp ascSeed_holds2.2 PositivityTheory.Rg.HF.GL.automorphicFormsFiniteGL hN hV hn e⟩
  subst ha
  exact ⟨π.V, PositivityTheory.RSHS.L1.cuspDiscrete E _ hN π (GlobalTheory.SpehPair.isUnitary_of_isNormalised hn) hn,
    PDich.ascEmb_one (Setoid.refl π)⟩
end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.BaseChangeIdentities

theorem speh (h : PositivityTheory.Rg.BcN.BaseChangeIsobaricN) : GlobalTheory.BcSpeh.BcSpeh := bcSpeh_of ascComp (definiteN_of h)

end UpperTheory.BaseChangeIdentities

end
