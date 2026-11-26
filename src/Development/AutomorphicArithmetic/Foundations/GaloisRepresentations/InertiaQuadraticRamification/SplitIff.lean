module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InertiaGenAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSplitAtOfDecompositionLeRestrictionRange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameKummerInertiaSurjective
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfiniteQuadraticCMGoodBaseChangeSplit

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.SplitIff
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.UnitaryBC
open scoped Pointwise

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem apply_eq_of_not_fixes {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    {s t : G (maximalRealSubfield L) Ω} (hs : ¬ Fixes L s) (ht : ¬ Fixes L t) (y : L) :
    s (algebraMap L Ω y) = t (algebraMap L Ω y) := by
  haveI : IsGalois (maximalRealSubfield L) L := Algebra.IsQuadraticExtension.isGalois _ _
  have hcard : Nat.card (L ≃ₐ[maximalRealSubfield L] L) = 2 := by
    rw [IsGalois.card_aut_eq_finrank]
    exact Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hne : ∀ r : G (maximalRealSubfield L) Ω, ¬ Fixes L r → r.restrictNormal L ≠ 1 := by
    intro r hr h1
    apply hr
    intro x
    rw [← AlgEquiv.restrictNormal_commutes r L x, h1]
    rfl
  have heq : s.restrictNormal L = t.restrictNormal L :=
    ((Nat.card_eq_two_iff' 1).1 hcard).unique (hne s hs) (hne t ht)
  rw [← AlgEquiv.restrictNormal_commutes s L y, ← AlgEquiv.restrictNormal_commutes t L y, heq]

theorem splitIff : SplitIff := by
  intro L Ω _ _ _ _ _ _ A w hA
  show IsSplitAt w ↔ ∀ g ∈ Dec (F := maximalRealSubfield L) A, Fixes L g
  have up : ∀ (B : ValuationSubring Ω) (u : HeightOneSpectrum (𝓞 L)), IsPlaceOver B u →
      IsPlaceOver B (HeightOneSpectrum.under (𝓞 (maximalRealSubfield L)) u) := by
    intro B u hB x
    have e : algebraMap (maximalRealSubfield L) Ω (x : maximalRealSubfield L) =
        algebraMap L Ω ((algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) x : 𝓞 L) : L) := by
      rw [IsScalarTower.algebraMap_apply (maximalRealSubfield L) L Ω]
      rfl
    rw [e, hB]
    simp [HeightOneSpectrum.under]
  have hv := up A w hA
  have val : ∀ (σ : G (maximalRealSubfield L) Ω) (y : Ω),
      (σ • A).valuation y < 1 ↔ A.valuation (σ⁻¹ y) < 1 := by
    intro σ y
    rw [valuation_lt_one_iff', valuation_lt_one_iff',
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    simp
  constructor
  · rintro ⟨u, hu, huw⟩ g hg
    by_contra hgL
    obtain ⟨A', hA'⟩ := exists_isPlaceOver Ω u
    obtain ⟨σ, rfl⟩ := exists_smul_eq_of_isPlaceOver hv (huw ▸ up A' u hA')
    apply hu
    refine eq_of_isPlaceOver hA' ?_
    intro x
    rw [val, ← hA x]
    by_cases hσ : Fixes L σ⁻¹
    · rw [hσ]
    · rw [apply_eq_of_not_fixes hσ hgL, valuation_apply_lt_one_iff hg]
  · intro h
    refine UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω A _ hv ?_ w rfl
    intro g hg
    refine ⟨AlgEquiv.ofRingEquiv (f := g.toRingEquiv) (fun x => h g hg x), ?_⟩
    ext x
    rfl

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.NonsplitOfSqrtConductor
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ValPrimeOfLt
theorem UpperTheory.Reformulated.B.Qi55.val_prime_of_lt :
    ∀ {Ω : Type} [inst : Field Ω]
    (A : ValuationSubring Ω) (n : ℕ),
    n ≠ (0 : ℕ) →
      (A.valuation : Ω → A.ValueGroup) (↑n : Ω) < (1 : A.ValueGroup) →
        ∃ (t : ℕ), Nat.Prime t ∧ t ∣ n ∧ (A.valuation : Ω → A.ValueGroup) (↑t : Ω) < (1 : A.ValueGroup) := by
  intro Ω _ A n
  induction n using induction_on_primes with
  | zero => intro h; exact absurd rfl h
  | one => intro _ h; simp at h
  | prime_mul p a hp ih =>
    intro hne h
    have ha : a ≠ 0 := right_ne_zero_of_mul hne
    by_cases hpv : A.valuation (p : Ω) < 1
    · exact ⟨p, hp, dvd_mul_right p a, hpv⟩
    · have hav : A.valuation (a : Ω) < 1 := by
        by_contra hc
        rw [Nat.cast_mul, map_mul] at h
        exact absurd h (not_lt.mpr (one_le_mul (not_lt.mp hpv) (not_lt.mp hc)))
      obtain ⟨t, ht, hd, hv⟩ := ih ha hav
      exact ⟨t, ht, hd.mul_left p, hv⟩
end

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion.WeylLatticeInDetCoeffSpan

private theorem val_prime_of_lt {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (n : ℕ) :
    n ≠ 0 → A.valuation (n : Ω) < 1 → ∃ t : ℕ, t.Prime ∧ t ∣ n ∧ A.valuation (t : Ω) < 1 :=
  _root_.UpperTheory.Reformulated.B.Qi55.val_prime_of_lt A n

section

variable {Y Ω : Type} [Field Y] [NumberField Y] [IsCMField Y] [Field Ω] [Algebra Y Ω] [IsAlgClosure Y Ω]

end

end UpperTheory.Gal.UnramifiedFromSplittingCriterion.WeylLatticeInDetCoeffSpan
end
