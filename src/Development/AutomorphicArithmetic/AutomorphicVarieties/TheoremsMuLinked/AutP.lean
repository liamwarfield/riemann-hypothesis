module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.FreeFlag
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.KatoTwoOfUseN

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.AutP
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp GlobalTheory.CuspRep

namespace UpperTheory.V.Th

def Unl (l : ℕ) [Fact l.Prime] {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {n : ℕ} (M : ℕ)
    (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧
    ∃ κ, Af.FlagAt M m r A κ ∧ ∀ i j, κ i ≠ κ j * (cycBar F Ω l).comp (Dec (F := F) A).subtype

def AutP {K Ω : Type} [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra K Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    (ι : Qbar l ≃+* ℂ) (r : G K Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∃ π : CuspSub K n, (CG.mk π).IsRegAlg ∧ (∃ χ, GlobalTheory.ContraPair.PolarizedPair π χ) ∧ Af.AttC ι r π

end UpperTheory.V.Th

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.LinkedRig
noncomputable section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

namespace UpperTheory.V.Th

def RigOver {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    {n : ℕ} (r : G L Ω →* GL (Fin n) (Qbar l)) (ka : G L Ω →* (Qbar l)ˣ) : Prop :=
  ∃ (s : W.HidaSetting l L Ω) (V : s.Lev) (ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)),
    (∀ g, W.mat ρ (V.pr g) = (ka g : Qbar l) • W.mat r g) ∧
    (∀ g g' : G L Ω, W.resP L Ω g' = s.c * W.resP L Ω g * s.c⁻¹ → ka g * ka g' = cycBar L Ω l g ^ (1 - (n : ℤ))) ∧ AdZero V ρ

section

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
  {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* c.Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
  {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField c.O)}

def RigPt (k : GalLink η Ψ σ g₁ B M L Φ) (n : ℕ) (ι : Qbar l ≃+* ℂ) (ka : G L Ω →* (Qbar l)ˣ) : Prop :=
  ∀ (A : Subalgebra c.O (PadicAlgCl l)) [IsDiscreteValuationRing A] [Module.Finite c.O A] [IsLocalHom (algebraMap c.O A)]
    (ρ : Fr.NRep Φ n A), IsLiftA c.O ρ →
    (∀ v i, ∀ g ∈ Φ.Iv v, (ρ.ψ v i g).val = algebraMap c.O A (Ψ (k.j v g) ^ Fr.w n i).val) →
    ∀ r : G L Ω →* GL (Fin n) (Qbar l), (∀ s, (r s).val = (ρ.r (k.p0 s)).map A.val) → IsIrr r → IsAutCsd ι (tw r ka) →
      FreeAt l r → RigOver r ka

end

def RigPtOf : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), LinkHyp c N e η σ B M →
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O))
    (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ)
    (c₁ : Coef l) [Fr.IsCoef l c₁.O] (f : ResidueField c.O →+* ResidueField c₁.O) (n : ℕ)
    (ka : G L Ω →* (Qbar l)ˣ) (_ : CReal k c₁ f n ka), W.Large L c₁ → IsKa σ M ι n ka → RigPt k n ι ka

def LinkedRig : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), LinkHyp c N e η σ B M →
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O)) (C₀ : ℕ)
    (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ), Φ.Ok C₀ → Φ.Big C₀ →
    SeedClause c η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ L →
    RigPt k 3 ι (cycBar L Ω l)⁻¹ ∧ ∃ ka, IsKa σ M ι 2 ka ∧ RigPt k 2 ι ka

end UpperTheory.V.Th

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.Number
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.Base UpperTheory.V.Alg

namespace UpperTheory.V.Th


open UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws in
def SpPt : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c), Ctx2 D ∨ Ctx3 D →
    ∀ r, D.EPt r → Irr r → ∃ T : Tower D, T.Fit ∧ T.Deep ∧ ∀ c₁ : Coef l,
      ∃ (c' : Coef l) (h : c.O ≤ c'.O) (X : Space (T.fr ∅) (inc h)) (y : X.A →ₐ[c'.O] PadicAlgCl l)
        (r₁ : G ℚ Ω →* M4 (PadicAlgCl l)), c₁.O ≤ c'.O ∧ IsConj4 r r₁ ∧ D.Mult r₁ ∧
        r₁.comp (resQ T.F) = (X.P.map (y : X.A →+* PadicAlgCl l)).r ∧
        T.Wts (fun i => 2 * D.wts4 i) (X.P.map (y : X.A →+* PadicAlgCl l)) ∧ Irr (r₁.comp T.L.fixingSubgroup.subtype)

end UpperTheory.V.Th

end
end
