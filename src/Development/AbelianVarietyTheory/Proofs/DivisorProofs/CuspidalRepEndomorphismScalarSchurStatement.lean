module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalRepEndomorphismScalarSchur
public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidalRep_endomorphism_scalar_schur : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (x : CuspSub E a) (f : x.V →ₗ[ℂ] x.V), (∀ o φ, f (x.op o φ) = x.op o (f φ)) → ∃ c : ℂ, ∀ φ, f φ = c • φ := by
  first | exact @GlobalTheory.CuspSchur.schur | exact GlobalTheory.CuspSchur.schur | (intros; apply GlobalTheory.CuspSchur.schur <;> assumption)
