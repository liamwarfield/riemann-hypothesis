module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

def AbelianHodgeDeRham : Prop :=
  ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    (Module.Finite R (HH1 A.hom) ∧ Module.Projective R (HH1 A.hom) ∧
      ∀ p : PrimeSpectrum R, Module.rankAtStalk (HH1 A.hom) p = 2 * g) ∧
    (∃ e : ⋀[R]^2 (HH1 A.hom) ≃ₗ[R] HH2 A.hom, ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = cupHH A.hom a b) ∧
    (Module.Finite R (GlobForm A.hom) ∧ Module.Projective R (GlobForm A.hom) ∧
      ∀ p : PrimeSpectrum R, Module.rankAtStalk (GlobForm A.hom) p = g) ∧
    (Module.Finite R (HO1 A.hom) ∧ Module.Projective R (HO1 A.hom) ∧
      ∀ p : PrimeSpectrum R, Module.rankAtStalk (HO1 A.hom) p = g) ∧
    (ClosedForm A.hom = ⊤ ∧ Function.Injective (clForm A.hom) ∧ Function.Surjective (toHO1 A.hom)) ∧
    ∀ (R' : Type) [CommRing R'] [Algebra R R'] (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ A.left)
      (h : IsPullback φ s' A.hom (spMap (algebraMap R R'))),
      (∃ e : R' ⊗[R] HH1 A.hom ≃ₗ[R'] HH1 s', ∀ c, IsPull1 h.w c (e (1 ⊗ₜ c))) ∧
      (∃ e : R' ⊗[R] GlobForm A.hom ≃ₗ[R'] GlobForm s', ∀ c, IsPullForm h.w c (e (1 ⊗ₜ c))) ∧
      ∃ e : R' ⊗[R] HO1 A.hom ≃ₗ[R'] HO1 s', ∀ c, IsPullO h.w c (e (1 ⊗ₜ c))

end GlobalTheory.Published
end
end

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCobOneOfIntegral
noncomputable section

open CategoryTheory WittVector Ideal TensorProduct Coalgebra

namespace GlobalTheory.PrismModel

open GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.Published

section Eps

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

private theorem zeta_add_pow_p_pow_eq_zeta (ε : PreTilt O p) (n k : ℕ) :
    zeta ε (n + k) ^ p ^ k = zeta ε n := by
  induction k with
  | zero => simp
  | succ k ih => rw [← add_assoc, pow_succ', pow_mul, zeta_succ_pow, ih]

theorem isPrimitiveSystem_of_one {ε : PreTilt O p} (h : IsPrimitiveRoot (zeta ε 1) p) :
    IsPrimitiveSystem ε := by
  intro n
  cases n with
  | zero =>
    rw [pow_zero, IsPrimitiveRoot.one_right_iff]
    have h0 := zeta_add_pow_p_pow_eq_zeta ε 0 1
    rw [zero_add, pow_one] at h0
    rw [← h0, h.pow_eq_one]
  | succ n =>
    have h1 : zeta ε (n + 1) ^ p ^ n = zeta ε 1 := by
      have h2 := zeta_add_pow_p_pow_eq_zeta ε 1 n
      rwa [add_comm 1 n] at h2
    rw [IsPrimitiveRoot.iff_orderOf]
    apply orderOf_eq_prime_pow
    · rw [h1]
      exact h.ne_one (Fact.out : p.Prime).one_lt
    · rw [pow_succ, pow_mul, h1, h.pow_eq_one]

end Eps

section Mu

variable {O A : Type} [CommRing O] [CommRing A] [Bialgebra O A]

variable {p : ℕ} [Fact p.Prime]

end Mu

end GlobalTheory.PrismModel
end
end
