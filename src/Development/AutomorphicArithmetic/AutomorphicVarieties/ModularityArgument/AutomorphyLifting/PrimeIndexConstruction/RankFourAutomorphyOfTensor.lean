module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.ThruBad
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.IsAutCsdA
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.PolFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.PlainAtRTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ClosedHeckeCosets.IsClosedSmall
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.SumDivHecke
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.OrdAway
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.OrdIrr

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.RankFourAutomorphyOfTensor
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S2 UpperTheory.V.Sd.S3 UpperTheory.V.Cu

namespace UpperTheory.V.Z.Win.Birth

theorem mkCsdW {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ} [IsCMField F]
    {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)} (h : UpperTheory.GalN.V.AutCsd0 ι r) (_ : Continuous r → WitA ι r) : IsAutCsd ι r := h

theorem mkCsdW' {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ} [IsCMField F]
    {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)} (h : UpperTheory.GalN.V.AutCsd0 ι r) (u : Continuous r → WitA ι r) : IsAutCsdA ι r := ⟨h, u⟩

def SphOfUnrW : Prop :=
  ∀ (M Ω : Type) [Field M] [NumberField M] [IsCMField M] [Field Ω] [Algebra M Ω] [IsAlgClosure M Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (r : G M Ω →* GL (Fin n) (Qbar l)) (π : CuspSub M n), Continuous r → Sol.Pol ι r →
    (CG.mk π).IsRegAlg → AttC ι r π → AllW ι r → ∀ w : HeightOneSpectrum (𝓞 M), ((l : ℕ) : 𝓞 M) ∉ w.asIdeal →
    ∀ A : ValuationSubring Ω, IsPlaceOver A w → (∀ s ∈ Ine (F := M) A, r s = 1) → ∃ B, (CG.mk π).HasSat w B

def BadOfW : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (K' L M : IntermediateField ℚ Ω)
    [NumberField L] [NumberField M] [IsCMField M] [Algebra L M] [IsScalarTower L M Ω] [IsAlgClosure M Ω] [IsGalois L M], M = K' ⊔ L →
    ∀ (ρ : G ℚ Ω →* GL (Fin 2) (Qbar l)) (r : G M Ω →* GL (Fin 2) (Qbar l)) (π : CuspSub M 2), GoodAt K' L ρ → Continuous r → Af.Sol.Pol ι r →
    (CG.mk π).IsRegAlg → AttC ι r π → AllW ι r →
    (∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := M) A, ρ (resQ M s) = 1 → r s = 1) → Z.InvariantSubmoduleMonicPolynomial.E.SplitBad L π

def IndAutLP : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T : Tower D)
    (k₀ : IntermediateField ℚ Ω) [NumberField k₀] [IsTotallyReal k₀] (φ : G ℚ Ω →* (Qbar l)ˣ) (ι : Qbar l ≃+* ℂ) (k t : ℕ)
    (r : G k₀ Ω →* GL (Fin 2) (Qbar l)) (α β : (Qbar l)ˣ) (R : G ℚ Ω →* GL (Fin 4) (Qbar l)) (δ : G T.F Ω →* (Qbar l)ˣ),
    IndDat T k₀ φ ι k t r α β R δ → PR ι r → IsAutC ι (R.comp (resQ T.L)) ∧ AllW ι (R.comp (resQ T.L))

def OffW {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (K' : IntermediateField ℚ Ω)
    (ρ : G ℚ Ω →* GL (Fin 2) (Qbar l)) (R : G ℚ Ω →* GL (Fin 4) (Qbar l)) : Prop :=
  ∀ (L : IntermediateField ℚ Ω) [NumberField L] [_root_.NumberField.IsTotallyComplex L], IsAbelianGalois ℚ L → ¬ K' ≤ L → GoodAt K' L ρ →
    IsIrr (R.comp (resQ L)) → AllW ι (R.comp (resQ L))

def RankFourAutomorphyOfTensor : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (K' : IntermediateField ℚ Ω) [NumberField K'], Module.finrank ℚ K' = 2 → IsTotallyComplex K' →
    ∀ ρ : G ℚ Ω →* GL (Fin 2) (Qbar l), Continuous ρ → IsAutR ι ρ → IrrOpen ρ → PR ι ρ →
    ∀ (g0 : G ℚ Ω) (m : ℕ) (c₁ : Coef l) (κ : G K' Ω →* (Qbar l)ˣ), g0 ∉ K'.fixingSubgroup →
    (∃ τ s, TauDat ι K' g0 (m * 1) c₁ τ s (κ ^ 1)) →
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ 9 ∧ ∀ (ρ₁ τ : G ℚ Ω →* M2 c₁.O) s, RepIso ρ (mapRep (algebraMap c₁.O (PadicAlgCl l)) ρ₁).toHomUnits →
      TauDat ι K' g0 (m * j) c₁ τ s (κ ^ j) → AutOffS ι K' ρ (tenB ρ₁ τ) ∧ OffW ι K' ρ (tenB ρ₁ τ)

def AwChain : Prop :=
  ∀ (F E M Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M]
    [Field Ω] [Algebra F E] [Algebra E M] [Algebra F Ω] [Algebra E Ω] [Algebra M Ω] [IsScalarTower F E Ω] [IsScalarTower E M Ω] [IsAlgClosure F Ω]
    [IsAlgClosure M Ω] [IsGalois E M] [Group.IsSolvable (M ≃ₐ[E] M)], Module.finrank F E = 2 → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (r : G F Ω →* GL (Fin 2) (Qbar l)) (κ : G E Ω →* (Qbar l)ˣ), Continuous r → PR ι r → Sd.IsAlgChar ι κ →
    IsIrr ((r.comp (galEmb F E Ω)).comp (galEmb E M Ω)) → AllW ι ((tw (r.comp (galEmb F E Ω)) κ).comp (galEmb E M Ω))

def PotOrd : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ)
    (r : G F Ω →* GL (Fin n) (Qbar l)) (m : Fin n → ℤ) (ψ : Fin n → G F Ω →* (Qbar l)ˣ) (κ : G F Ω →* (Qbar l)ˣ), (∀ i j, m i ≠ m j + 1) →
    (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → OrdAt r m ψ A) →
    ∀ v : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → PotUnl (tw r κ) v

end UpperTheory.V.Z.Win.Birth
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.AwOne
theorem UpperTheory.V.Z.Win.Birth.awOne :
    UpperTheory.V.Z.Win.Birth.AwOne := by
  intro F Ω _ _ _ _ _ _ l _ n hn ι r π hπ hwin π' _ hπ'
  obtain ⟨t, ht⟩ := hwin
  refine ⟨t, fun v => UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.suppSmo F n hn π π' ?_ t v (ht v)⟩
  filter_upwards [hπ.2, hπ'.2] with w h1 h2
  obtain ⟨B, hB, hE⟩ := h1
  obtain ⟨B', hB', hE'⟩ := h2
  have e : B = B' := (UpperTheory.hecke_eigenvalue_basic_properties F Ω l ι w).2.2 n r B B' hE hE'
  exact ⟨B, hB, e ▸ hB'⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.DirGNeOne
open UpperTheory.V.Z.Win.Birth

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published

namespace UpperTheory.V.Sd.EG

section Norm

variable {l : ℕ} [hl : Fact l.Prime]

variable (l) in
private def U : Subgroup (Qbar l)ˣ where
  carrier := {u | ‖(u : Qbar l) - 1‖ < 1}
  one_mem' := by simp
  mul_mem' {u v} hu hv := by
    have e : ((u * v : (Qbar l)ˣ) : Qbar l) - 1 = u * (v - 1) + (u - 1) := by push_cast; ring
    show ‖_‖ < 1
    rw [e]
    refine small_add ?_ hu
    rw [norm_mul, norm_eq_one_of hu, one_mul]
    exact hv
  inv_mem' {u} hu := by
    have e : (u : Qbar l) * (((u⁻¹ : (Qbar l)ˣ) : Qbar l) - 1) = -(u - 1) := by rw [mul_sub, Units.mul_inv]; ring
    have := congrArg norm e
    rw [norm_mul, norm_eq_one_of hu, one_mul, norm_neg] at this
    show ‖_‖ < 1
    rw [this]
    exact hu

end Norm

section Gal

variable {l : ℕ} [hl : Fact l.Prime] {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

end Gal

end UpperTheory.V.Sd.EG
end
