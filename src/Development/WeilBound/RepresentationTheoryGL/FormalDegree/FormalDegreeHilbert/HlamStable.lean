module

public import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.HlamStable
public import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.MomB
public import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.InConeRefl
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.KSchur

@[expose] public section

noncomputable section

open Finset MeasureTheory Matrix
open scoped InnerProductSpace ComplexOrder

namespace PositivityTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

export CompanionTheory.RgFd (
  cK pP phiK hI Dz CoefPow KNull HsPol PhiMul PhiLe PhiCont HsInt DegPsi NormAt
  GapNorm NormInd NormDef PsiNorm
)

def HsPs : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (Λ : Fin n → ℝ) (T : KType ε Λ) (μ : Fin n → ℤ) (x : Matrix (Fin n) (Fin n) ℂ), x.PosDef →
    hsOp (psM T μ x) = (Module.finrank ℂ T.V : ℝ) ^ 2 * ∫ p, hI T μ x p ∂((dk ε).prod (dk ε))

def KmapZero : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (T : KType ε (lowK ε lam))
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)), IsHCParam lam → IsPsiFor ε lam T Ψ →
    Formalism.MainNotions.S.IsDS ε lam (sigLam ε Ψ T.w) → ∀ B : T.V →ₗ[ℂ] L2 ε,
    (∀ (k : KG ε) (v : T.V), B (T.op k v) = rreg ε (toMK k) (B v)) → (∀ v, B v ∈ Hlam ε Ψ T.w) →
    (∀ v v' : T.V, ⟪B v', uniformisationL2 ε Ψ T.w v⟫_ℂ = 0) → B = 0

def HlamStable : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (T : KType ε (lowK ε lam))
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)), IsPsiFor ε lam T Ψ →
    ∀ g ∈ UJset ε, ∀ x ∈ Hlam ε Ψ T.w, rreg ε g x ∈ Hlam ε Ψ T.w

def FormF : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (T : KType ε (lowK ε lam))
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)), IsHCParam lam → IsPsiFor ε lam T Ψ →
    Formalism.MainNotions.S.IsDS ε lam (sigLam ε Ψ T.w) → ∀ g ∈ UJset ε, ∀ v v' : T.V,
    ⟪uniformisationL2 ε Ψ T.w v', rreg ε g (uniformisationL2 ε Ψ T.w v)⟫_ℂ = ((‖uniformisationL2 ε Ψ T.w T.w‖ ^ 2 : ℝ) : ℂ) * ⟪v', Ψ g v⟫_ℂ

def ModelDS : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ), IsHCParam lam → IsMu lam μ →
    IsPsiFor ε lam T (PsiM T μ) ∧ Formalism.MainNotions.S.IsDS ε lam (sigLam ε (PsiM T μ) T.w)

def FdModel : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ), IsHCParam lam → IsMu lam μ →
    Formalism.MainNotions.S.IsFdeg (muCD ε) (sigLam ε (PsiM T μ) T.w) (dimVlam lam)

def FdAll : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), IsHCParam lam → ∀ (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ →
    Formalism.MainNotions.S.IsFdeg (muCD ε) σ (dimVlam lam)

end PositivityTheory.RgFd
