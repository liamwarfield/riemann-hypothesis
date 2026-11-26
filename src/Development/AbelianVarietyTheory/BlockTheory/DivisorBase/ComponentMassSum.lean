module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMassSum
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

open NumberField IsDedekindDomain MeasureTheory Module ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions
  Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt
open scoped TensorProduct

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D)
  (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r)

def IsComplexData : Prop :=
  l.A = 1 ∧ ∀ σ, GoodEmb c σ → IsUnf (U σ) ∧
    (∃ Kf th hr, IsLevelK (V σ) l.M Kf ∧ (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧
      DictIsUnif (V σ) (dict σ) Kf th hr) ∧
    FinVol (V σ) ∧ ∀ k (τ : D.host.E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = xiR D

def partLat (Z : Comp Xo c) (G : WTZ D.host.E) : Submodule (𝓞 c.F) (cuspW Xo c U G) :=
  (latOn U Z G).map ((Submodule.inclusion (cuspOn_le U Z G)).restrictScalars (𝓞 c.F))

def normRes (Z : Comp Xo c) (G : WTZ D.host.E) (σ : c.F →+* ℂ) (f : cuspOn U Z G) : ℝ :=
  petW U (xiR D) V dict G σ f

attribute [local instance high] Submodule.module

def degRes (Z : Comp Xo c) (G : WTZ D.host.E) : ℝ :=
  GlobalTheory.AllWt.deg (normRes U V dict Z G) (latOn U Z G)

def mass (Z : Comp Xo c) (σ : c.F →+* ℂ) : ℝ :=
  (muQ1 (V (goodOf c σ))
    (classesOver (V (goodOf c σ)) (dict (goodOf c σ)) (framesOn (U (goodOf c σ)) Z))).toReal

def Splits (G : WTZ D.host.E) : Prop :=
  (∀ F : cuspW Xo c U G, (F : Rul Xo c) = ∑ᶠ Z : Comp Xo c, FlatLine.idem Z * (F : Rul Xo c) ∧
    ∃ h : ∀ Z : Comp Xo c, FlatLine.idem Z * (F : Rul Xo c) ∈ cuspOn U Z G,
      (F ∈ latW U G ↔ ∀ Z, (⟨_, h Z⟩ : cuspOn U Z G) ∈ latOn U Z G)) ∧
  (iSupIndep (fun Z : Comp Xo c => cuspOn U Z G) ∧ ⨆ Z : Comp Xo c, cuspOn U Z G = cuspW Xo c U G) ∧
  iSupIndep (fun Z : Comp Xo c => partLat U Z G) ∧ ⨆ Z : Comp Xo c, partLat U Z G = latW U G

def Orthogonal (G : WTZ D.host.E) : Prop :=
  ∀ σ : c.F →+* ℂ,
    (∀ f : ∀ Z : Comp Xo c, cuspOn U Z G,
      petW U (xiR D) V dict G σ (∑ᶠ Z, (f Z : Rul Xo c)) ^ 2 = ∑ᶠ Z, normRes U V dict Z G σ (f Z) ^ 2) ∧
    ∀ (Z : Comp Xo c) (f : cuspOn U Z G),
      normRes U V dict Z G σ f ^ 2 = mass U V dict Z σ * normOn U (xiR D) V dict Z G σ f ^ 2

def Adds (G : WTZ D.host.E) : Prop :=
  (GoodW U (xiR D) V dict G ↔ ∀ Z, GoodOn U (xiR D) V dict Z G) ∧
  (GoodW U (xiR D) V dict G →
    (∀ Z, HasGram (normRes U V dict Z G)) ∧
    rankW U G = ∑ᶠ Z : Comp Xo c, rankOn U Z G ∧
    degW U (xiR D) V dict G = ∑ᶠ Z : Comp Xo c, degRes U V dict Z G ∧
    (∀ Z, rankOn U Z G ≠ 0 → ∀ σ, 0 < mass U V dict Z σ) ∧
    degW U (xiR D) V dict G = ∑ᶠ Z : Comp Xo c, (degOn U (xiR D) V dict Z G -
      (rankOn U Z G : ℝ) / 2 * ((∑ σ : c.F →+* ℂ, Real.log (mass U V dict Z σ)) / (finrank ℚ c.F : ℝ))))

theorem finite_comp : Finite (Comp Xo c) := CompFin.finite_comp Xo c

theorem partLat_le (Z : Comp Xo c) (G : WTZ D.host.E) : partLat U Z G ≤ latW U G := by
  rintro _ ⟨f, hf, rfl⟩
  exact (mem_latOn U).1 hf

end GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum
end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TameInvariantLevelAction
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev OAf (D : D7) : Subring (EAf D) := Formalism.L2.Herm.intAf D.host.F D.host.E

def finR (V : HSp D) {r : ℕ} (hr : V.rank = r) : GA D V →* GL (Fin r) (EAf D) :=
  (Units.map (Matrix.reindexRingEquiv (EAf D) (finCongr hr)).toRingHom.toMonoidHom).comp (finE V)

def IsLatBasis (V : HSp D) {r : ℕ} (hr : V.rank = r) (β : GL (Fin r) (EAf D)) : Prop :=
  ∀ z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E, z ∈ latHat V ↔
    ∀ i, (Units.val (β⁻¹ : GL (Fin r) (EAf D))).mulVec
      (fun a => swapAE D (z (Fin.cast hr.symm a))) i ∈ OAf D

end GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts
end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.AdaptedStandardBasis
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightData

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt

section Weights

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)

def IsThetaWt (la : Weight Dw) (n : ℕ) : Prop :=
  8 ∣ n ∧ (∀ τ, Antitone (la τ)) ∧
    (∀ τ (i : Fin (Dw.p + Dw.q)), (i : ℕ) < Dw.p → ((n / 2 : ℕ) : ℤ) ≤ la τ i) ∧
    (∀ τ (i : Fin (Dw.p + Dw.q)), Dw.p ≤ (i : ℕ) → la τ i ≤ -((n / 2 : ℕ) : ℤ)) ∧
    ∀ τ (i k : Fin (Dw.p + Dw.q)), (i : ℕ) + 1 = Dw.p → (k : ℕ) = Dw.p → (n : ℤ) + 2 < la τ i - la τ k

end Weights

section Family

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H}

variable (Xo : Moduli Dw l) (c : Coeff l)

def polyNorm {n : ℕ} (P : MvPolynomial (LtN Dw n) c.F) : ℝ :=
  Real.sqrt (∑ s : c.F →+* ℂ, ∑ m ∈ P.support, ‖s (P.coeff m)‖ ^ 2)



variable {Xo c} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

end Family

section Constants

variable (D : D7) (large₂ : SizeData₂ D)

end Constants

section Statement

variable (D : D7) (large₂ : SizeData₂ D)

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}

end Statement

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightData
end
end
