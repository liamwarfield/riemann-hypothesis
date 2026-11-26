module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ValuationCoeEqNorm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.CMVal

variable {E : Type} [Field E] [NumberField E]

def IsCMType {I : Type} (φ : I → E →+* ℂ) : Prop :=
  ∀ σ : E →+* ℂ, ∃! i, σ = φ i ∨ σ = ComplexEmbedding.conjugate (φ i)

def UnramFin (E : Type) [Field E] [NumberField E] : Prop := differentIdeal (OF E) (𝓞 E) = ⊤

def Over (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (OF E)) : Prop :=
  P.asIdeal.comap (algebraMap (OF E) (𝓞 E)) = v.asIdeal

def Splits (v : HeightOneSpectrum (OF E)) : Prop := ∃ P P' : HeightOneSpectrum (𝓞 E), P ≠ P' ∧ Over P v ∧ Over P' v

def expIn (𝔣 : Ideal (OF E)) (v : HeightOneSpectrum (OF E)) : ℕ := multiplicity v.asIdeal 𝔣

def IsBaseCond (𝔣 : Ideal (OF E)) : Prop :=
  𝔣 ≠ ⊥ ∧ 𝔣 ≠ ⊤ ∧ ∀ v : HeightOneSpectrum (OF E), v.asIdeal ∣ 𝔣 → Splits v ∧ expIn 𝔣 v ≤ 2 ∧
    ∃ l : ℕ, l.Prime ∧ l ≠ 2 ∧ (l : OF E) ∈ v.asIdeal ∧ ¬ (l : ℤ) ∣ discr E ∧
      ∀ P : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ P.asIdeal → Ideal.absNorm P.asIdeal = l

def IsFinSetSplitPlacesCoprimeConductor (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) : Prop :=
  ∀ q ∈ Q, Splits q ∧ ¬ q.asIdeal ∣ 𝔣

def condQ (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) : Ideal (OF E) := 𝔣 * ∏ q ∈ Q, q.asIdeal

def IsValChar {I : Type} [Fintype I] (φ : I → E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E))
    (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E) : Prop :=
  IsUnitary χ ∧ TrivOnF χ ∧ HasInf χ φ (fun i => (κ i : ℤ) + s) ∧
    ∀ (v : HeightOneSpectrum (OF E)) (P : HeightOneSpectrum (𝓞 E)), Over P v →
      (v ∈ Q → LevelLe χ P 1) ∧ (v ∉ Q → ExpAt χ P (expIn 𝔣 v))

def IntAt (l : ℕ) (a : ℂ) : Prop := ∃ n : ℕ, n.Coprime l ∧ IsIntegral ℤ ((n : ℂ) * a)

def UnitAt (l : ℕ) (a : ℂ) : Prop := a ≠ 0 ∧ IntAt l a ∧ IntAt l a⁻¹

def LInf {I : Type} [Fintype I] (m : I → ℤ) (s : ℂ) : ℂ :=
  ∏ i, (2 * (2 * (Real.pi : ℂ)) ^ (-(s + (|m i| : ℤ))) * Complex.Gamma (s + (|m i| : ℤ)))

end GlobalTheory.CMVal
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.MemMixedTsub
noncomputable section

open WittVector Ideal Matrix

namespace GlobalTheory.Sandwich.Model

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

theorem xi_eq (ε : PreTilt O p) : xi ε = ReciprocityTheory.PGsh.Ainf.xi p O ε := rfl

theorem nu_eq (ε : PreTilt O p) : nu ε = ReciprocityTheory.PGsh.Ainf.nu p O ε := rfl

section Field

variable {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C NNReal} [Algebra O C]
  (hv : v.Integers O) {ε : PreTilt O p}
  (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)
include hv hε

theorem theta_mu : fontaineTheta O p (mu ε) = 0 := by
  rw [← xi_mul_nu, map_mul, xi_eq, ReciprocityTheory.PGsh.Ainf.theta_xi p O hv ε hε, zero_mul]

theorem mu_ne_zero : mu ε ≠ 0 := by
  intro h
  rw [← xi_mul_nu, mul_comm] at h
  have := ReciprocityTheory.PGsh.Ainf.xi_nzd p O hv ε hε _ h
  exact ReciprocityTheory.PGsh.Ainf.theta_nu p O hv ε hε (by rw [← nu_eq, this, map_zero])

omit hε [IsAlgClosed C] in
theorem isDomain_Ainf : IsDomain (Ainf p O) := by
  haveI : IsDomain (PreTilt O p) := PreTilt.isDomain C v O hv p
  infer_instance

variable {h : ℕ} {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ] (D : Datum ε h Λ)

end Field

end GlobalTheory.Sandwich.Model
end
end
