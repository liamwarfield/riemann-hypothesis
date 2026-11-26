module

public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Formalism.SatakeDualWeyl.StatementG

@[expose] public section

section -- merged from Formalism.LocalToGlobal.GaloisLevelStructure.DefsFinTyp
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP

namespace Formalism.L2.NG

variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)

structure FinTyp where
  S : Submodule ℂ (GAf L n → ℂ)
  stable : ∀ h, ∀ f ∈ S, rt L n h f ∈ S
  smooth : ∀ f ∈ S, ∃ N : ℕ, 0 < N ∧ ∀ κ, Cong L n N κ → rt L n κ f = f
  ne : S ≠ ⊥
  irr : ∀ S' : Submodule ℂ (GAf L n → ℂ), S' ≤ S → (∀ h, ∀ f ∈ S', rt L n h f ∈ S') → S' = ⊥ ∨ S' = S

variable {L n}

def FinTyp.Iso (π π' : FinTyp L n) : Prop := IsoRep π.S π'.S

end Formalism.L2.NG
end
end

section -- merged from Formalism.LocalToGlobal.GaloisLevelStructure.DefsAutLoc
section -- merged from Formalism.AlgebraicWeights.InertDatumExists
noncomputable section

open NumberField IsDedekindDomain Polynomial Filter TensorProduct

namespace Formalism.AUTREP

section Inert

variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)

local notation3 "L⁺" => maximalRealSubfield L

open ReciprocityTheory.Aut

structure InertDatum (v : HeightOneSpectrum (𝓞 L⁺)) (w : HeightOneSpectrum (𝓞 L)) where
  e : L ⊗[L⁺] v.adicCompletion L⁺ ≃+* w.adicCompletion L
  σw : w.adicCompletion L →+* w.adicCompletion L
  ϖ : w.adicCompletion L
  P : GL (Fin n) (w.adicCompletion L)
  comm : ∀ x, e (Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom (v.adicCompletion L⁺) x) = σw (e x)
  unram : Formalism.UG.IsUnramInv ϖ σw (Formalism.UG.qV L⁺ v)
  integ : ∀ x, x ∈ Formalism.UG.tensInt (F := L⁺) (v.adicCompletion L⁺) (Formalism.UG.intOE L) (Formalism.UG.Ov L⁺ v) ↔
    e x ∈ Formalism.UG.intL (w.adicCompletion L)
  Pint : P ∈ (Formalism.UG.bc (n := Fin n) (Formalism.UG.intL (w.adicCompletion L)).subtype).range
  Panti : Formalism.UG.cT σw (P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) * (P : Matrix (Fin n) (Fin n) _) =
    Formalism.UG.antiJ (w.adicCompletion L) n

variable {L n}

def InertDatum.loc {v : HeightOneSpectrum (𝓞 L⁺)} {w : HeightOneSpectrum (𝓞 L)} (D : InertDatum L n v w)
    (x : GAf L n) : GL (Fin n) (w.adicCompletion L) :=
  D.P⁻¹ * Formalism.UG.bc (n := Fin n) (D.e : L ⊗[L⁺] v.adicCompletion L⁺ →+* w.adicCompletion L)
    (Matrix.GeneralLinearGroup.map (compAt L v) (x : GL (Fin n) (AL L))) * D.P


open Classical in
def InertDatum.hval {v : HeightOneSpectrum (𝓞 L⁺)} {w : HeightOneSpectrum (𝓞 L)} (D : InertDatum L n v w)
    (h : Formalism.UG.GU D.σw n → ℂ) (y : GL (Fin n) (w.adicCompletion L)) : ℂ :=
  if hy : y ∈ Formalism.UG.GU D.σw n then h ⟨y, hy⟩ else 0

variable (L n)


open Classical in
def heckeFunI {W : Type} [AddCommGroup W] [Module ℂ W] (U : Subgroup (GAf L n))
    {v : HeightOneSpectrum (𝓞 L⁺)} {w : HeightOneSpectrum (𝓞 L)} (D : InertDatum L n v w)
    (h : Formalism.UG.GU D.σw n → ℂ) (f : GAf L n → W) : GAf L n → W :=
  fun g => ∑ᶠ c : GAf L n ⧸ U,
    if hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside (L := L) {v} x then
      D.hval h (D.loc hc.choose) • f (g * hc.choose) else 0


end Inert

end Formalism.AUTREP
end
end

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP

namespace Formalism.L2.NG

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

local notation3 "L⁺" => maximalRealSubfield L

def SatAt (π : AutRep L n) {v : HeightOneSpectrum (𝓞 L⁺)} {w : HeightOneSpectrum (𝓞 L)} (Dv : InertDatum L n v w)
    (α : Fin (n / 2) → ℂ) : Prop :=
  ∃ f ∈ π.S, f ≠ 0 ∧ ∃ U : Subgroup (GAf L n), (∀ κ ∈ U, rt L n κ f = f) ∧
    (∀ κ, TrivOutside (L := L) {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) ∧
    ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n),
      heckeFunI L n U Dv h f = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV L⁺ v) h α • f

end Formalism.L2.NG
end
end
