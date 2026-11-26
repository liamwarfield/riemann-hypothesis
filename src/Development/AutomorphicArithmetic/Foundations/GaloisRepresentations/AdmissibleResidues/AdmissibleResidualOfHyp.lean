module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.PolarizedAutomorphicOfAutP
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.LevelFRes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.QuadraticInductionGL2Alt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.AdmissibleResidualOfHyp
noncomputable section

open NumberField IsDedekindDomain IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr

namespace UpperTheory.GalN.V

theorem dual_two {Γ k : Type} [Group Γ] [Field k] (W : Γ →* GL (Fin 2) k) : DualTw W (Matrix.GeneralLinearGroup.det.comp W) :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; -1, 0] (by simp), fun s => by
    have hd : ((Matrix.GeneralLinearGroup.det.comp W s : kˣ) : k) = (W s).val.det := rfl
    rw [hd, Matrix.det_fin_two (W s).val]
    ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp <;> ring⟩

section
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
  {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N}

def IsModularN (_ : Dat Ω K c e ψ) (ι : Qbar l ≃+* ℂ) (W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l)) : Prop :=
  (∃ f : Af.Newform (2 * e + 1), f.Att ι (Af.tw W (cycBar ℚ Ω l ^ (-(e : ℤ))))) ∧ WitQ ι W

variable {D : Dat Ω K c e ψ} {ι : Qbar l ≃+* ℂ} {W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l)}

end

def AutEnd2N {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (c : Coef l) (η : G ℚ Ω →* ℤˣ)
    (Ψ : G ℚ Ω →* c.Oˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (e : ℕ) (ι : Qbar l ≃+* ℂ) : Prop :=
  ∀ (A : Subalgebra c.O (PadicAlgCl l)) [IsDiscreteValuationRing A] [Module.Finite c.O A]
    (r : G ℚ Ω →* U3.GG (m := 3) (R := A)),
    OrdPt l η Ψ σ g₁ B r → TypeII η (UnitaryThreeInertia.push A.val r) → (∀ g ∈ η.ker, (r g).mat 1 1 = 1) →
    ∀ W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l),
      (∀ g ∈ η.ker, (W g).val = corner (UnitaryThreeInertia.push A.val r g).mat) →
      (W σ).val.trace = 0 →
      (∃ f : Af.Newform (2 * e + 1), f.Att ι (Af.tw W (cycBar ℚ Ω l ^ (-(e : ℤ))))) ∧ WitQ ι W

end UpperTheory.GalN.V
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SeedDefs
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S2

namespace UpperTheory.GalN.V

def PropEGN : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (c : G ℚ Ω), Sd.IsCC c →
    ∀ (N w : ℕ) (φ θ : G ℚ Ω →* (Qbar l)ˣ), SlopeTestRemainingChoices N w θ → SplitAt N w φ → φ ≠ 1 → ∃ k₀ : ℕ, ∀ k ≥ k₀, φ c = (-1) ^ k →
      ∃ ρ, EisRep ι φ θ k ρ ∧ RW ι ρ

section
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} (T : Tower D)

def Wts0 (h : Fin 4 → ℤ) (P : PD T.ι (G T.F Ω) (PadicAlgCl l)) : Prop :=
  ∃ U : Subgroup (G T.F Ω), IsOpen (U : Set (G T.F Ω)) ∧ ∀ v i, ∀ s ∈ U ⊓ Ine (F := T.F) (T.pl v),
    P.ψ v i s ^ 2 = ((cycBar T.F Ω l s ^ h i : (PadicAlgCl l)ˣ) : PadicAlgCl l)

variable {T} {h : Fin 4 → ℤ} {P : PD T.ι (G T.F Ω) (PadicAlgCl l)}

theorem mkWts (k : Wts0 T h P) (_ : h 1 + 4 ≤ h 0 → haveI := T.nF; Unlinked P.r.toHomUnits) : T.Wts h P := k
theorem mkWts4 (k : Wts0 T (fun i => 2 * D.wts4 i) P) : T.Wts (fun i => 2 * D.wts4 i) P :=
  mkWts k fun hb => absurd hb (by simp [Raw.wts4]; omega)
end

end UpperTheory.GalN.V
end
end
