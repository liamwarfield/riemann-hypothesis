module

public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GaloisOfPrimePowerDegree

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FRatioSelf
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.EtProj

variable {R : Type} [CommRing R] {X : Scheme.{0}} {N : ℕ} (ι : X ⟶ PSpace R N)

def fOpen (g : MvPolynomial (Fin (N + 1)) R) : X.Opens := ι ⁻¹ᵁ Proj.basicOpen (grading R N) g

def fRatio {n : ℕ} (f g : MvPolynomial (Fin (N + 1)) R) (hf : f ∈ grading R N n) (hg : g ∈ grading R N n) :
    Γ(X, fOpen ι g) :=
  (ι.app (Proj.basicOpen (grading R N) g)).hom (GlobalTheory.ProjFrac.frac (grading R N) _ f g hf hg le_rfl)

theorem fRatio_self {n : ℕ} (g : MvPolynomial (Fin (N + 1)) R) (hg : g ∈ grading R N n) :
    fRatio ι g g hg hg = 1 := by
  unfold fRatio
  rw [GlobalTheory.ProjFrac.frac_self]
  exact map_one _

theorem mem_fOpen (g : MvPolynomial (Fin (N + 1)) R) (z : X) :
    z ∈ fOpen ι g ↔ g ∉ (ι.base z).asHomogeneousIdeal := Iff.rfl

end GlobalTheory.EtProj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsLocalRingOfIsIntegralOfHenselian
open CategoryTheory Limits AlgebraicGeometry IsLocalRing GlobalTheory.EtC TensorProduct

namespace GlobalTheory.IntClLocal

theorem isLocalRing_of_isIntegral_of_henselian (O : Type) [CommRing O] [HenselianLocalRing O]
    (S : Type) [CommRing S] [IsDomain S] [Algebra O S] [Algebra.IsIntegral O S] : IsLocalRing S := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  have : Module.Finite O (Algebra.adjoin O {a}) :=
    Algebra.finite_adjoin_simple_of_isIntegral (Algebra.IsIntegral.isIntegral a)
  have := GlobalTheory.TameKummer.isLocalRing_of_finite O (Algebra.adjoin O {a})
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self
    (⟨a, Algebra.self_mem_adjoin_singleton O a⟩ : Algebra.adjoin O {a}) with h | h
  · exact Or.inl (h.map (Algebra.adjoin O {a}).val)
  · exact Or.inr (by simpa using h.map (Algebra.adjoin O {a}).val)

end GlobalTheory.IntClLocal
end
