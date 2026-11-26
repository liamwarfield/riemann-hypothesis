module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.NontrivInf

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HermitianConvolution.HermInf
noncomputable section

namespace PositivityTheory.Rg.BcB.F.FBL

def HermInf : Prop := ∀ (n : ℕ) (lam : Fin n → ℤ), PositivityTheory.RgBcC.IsHerm (PositivityTheory.RgBcC.infOf lam)

theorem hermInf_holds : HermInf := by
  intro n lam
  refine ⟨Equiv.refl _, fun a => ?_⟩
  simp only [PositivityTheory.RgBcC.infOf, Equiv.refl_apply, Bool.false_eq_true, if_false, if_true, map_mul, map_add (f := _), map_sub,
    map_div₀, map_one, map_neg, map_intCast, Complex.conj_natCast, map_ofNat]
  ring

end PositivityTheory.Rg.BcB.F.FBL

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HermitianConvolution.EllHomPf
noncomputable section

open MeasureTheory
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.FBL

theorem ellHom_holds : EllHom := by
  intro E _ _ _ a b _ _ μ₁ μ₂ c φ
  unfold ellSum2
  rw [mul_finsum]
  refine finsum_congr fun q => ?_
  rw [finsum_eq_if, finsum_eq_if]
  split_ifs with hP
  swap
  · simp
  unfold orbTerm2 PositivityTheory.Rg.Tf.Loc.quotIntegral
  split_ifs with hρ
  · simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul c _
  · simp

end PositivityTheory.Rg.BcB.F.FBL

end
end
