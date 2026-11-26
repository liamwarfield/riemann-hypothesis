module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaNumberSU
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.HcFormalDegreeOfDiscreteSeriesFormalDegree
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrasadVolumeSU

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RosatiNormLEOfStarNormLE
section -- merged from Development.AbelianVarietyTheory.BlockTheory.CMModuli.FirstOrderRigidityLevel
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.FirstOrderRigidityLevel

abbrev Sp (R : Type) [CommRing R] : Scheme.{0} := Spec (CommRingCat.of R)

def Conv (g n k : ℕ) : Prop :=
  n.Prime ∧ Odd n ∧ 2 ≤ k ∧ 1 + 2 * (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2) < (((n ^ k) ^ 2 : ℕ) : ℝ)

section General
variable {S : Scheme.{0}}

end General

section Forms
variable {R : Type} [CommRing R] {P : PolAV (Sp R)} {I : Type} {e : ℤ}

end Forms

section Norm
variable {K : Type} [Field K] (P : PolAV (Sp K))

def HasTrace (ψ : P.A ⟶ P.A) (t : ℤ) : Prop :=
  ∀ M : ℕ, (M : K) ≠ 0 → ∀ y : Fin (2 * P.g) → (baseOver (Sp K) ⟶ P.A), (∀ i, y i ^ M = 1) →
    (∀ z : baseOver (Sp K) ⟶ P.A, z ^ M = 1 → ∃ c : Fin (2 * P.g) → ℕ, linComb y c = z) →
    ∀ B : Matrix (Fin (2 * P.g)) (Fin (2 * P.g)) ℕ,
      (∀ i, y i ≫ ψ = linComb y fun l => B l i) → ((B.trace : ℕ) : ZMod M) = (t : ZMod M)

end Norm

end GlobalTheory.IndefiniteRowSideFullHecke.FirstOrderRigidityLevel
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

def EndCharPolySt : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Sp K)) (ψ : P.A ⟶ P.A), IsMonHom ψ →
    ∃ χ : Polynomial ℤ, χ.Monic ∧ χ.natDegree = 2 * P.g ∧ ∀ l r : ℕ, l.Prime → (l : K) ≠ 0 →
      ∀ y : Fin (2 * P.g) → (baseOver (Sp K) ⟶ P.A), (∀ i, y i ^ l ^ r = 1) →
        (∀ z : baseOver (Sp K) ⟶ P.A, z ^ l ^ r = 1 → ∃ c : Fin (2 * P.g) → ℕ, linComb y c = z) →
        ∀ B : Matrix (Fin (2 * P.g)) (Fin (2 * P.g)) (ZMod (l ^ r)),
          (∀ i, y i ≫ ψ = linComb y fun k => (B k i).val) → B.charpoly = χ.map (Int.castRingHom (ZMod (l ^ r)))

def RosatiPositiveSt : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Sp K)) (φ φ' : P.A ⟶ P.A), IsMonHom φ → IsMonHom φ' →
    RosatiAdj P.A P.L φ φ' → φ ≠ 1 → ∀ t : ℤ, IndefiniteRowSideFullHecke.FirstOrderRigidityLevel.HasTrace P (φ' ≫ φ) t → 0 < t

end GlobalTheory.Published

namespace GlobalTheory.ThetaDetCompare

open GlobalTheory.IndefiniteRowSideFullHecke

section AdjRing

open CechPic MulOpposite

variable {K : Type} [Field K] {P : PolAV (Sp K)}





end AdjRing

section Trace

open ThetaCoord

variable {K : Type} [Field K] {P : PolAV (Sp K)} {M : ℕ} {y : Fin (2 * P.g) → (baseOver (Sp K) ⟶ P.A)}
  {O : Type} [Ring O]

variable [IsAlgClosed K]

end Trace

section Positive

variable {K : Type} [Field K] [IsAlgClosed K] {P : PolAV (Sp K)} {O : Type} [Ring O] [StarRing O]

end Positive

end GlobalTheory.ThetaDetCompare
end
end

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.RosatiTraces.RosatiTracePosStIff
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

def RosatiTracePosSt : Prop := RosatiPositiveSt

namespace RosatiTracePosSt

open GlobalTheory.ThetaDetCompare GlobalTheory.ThetaCoord

variable {K : Type} [Field K] [IsAlgClosed K]

end RosatiTracePosSt

end GlobalTheory.Published
end
end

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.RosatiTraces.TateCharPolyStIffIsCharPoly
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

def TateCharPolySt : Prop := EndCharPolySt

end GlobalTheory.Published

namespace GlobalTheory.TateCharPoly

open ThetaDetCompare ThetaCoord

variable {K : Type} [Field K] {P : PolAV (Sp K)}

variable [IsAlgClosed K]

end GlobalTheory.TateCharPoly
end
end

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsLeKsOfGood
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.Cyc

namespace GlobalTheory.Published

def FontaineEtale : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), GlobalTheory.Per.IsStd P AI →
    ∀ (K : FinExt l) (s : ℕ) (io : PowerSeries ℤ_[l] →ₐ[ℤ_[l]] Ainf l), IsIo (AI.εroot s) io →
      (∀ (LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)),
        ∃ (n : ℕ) (d : Fin n → TW (RW LL) T),
          (∀ i, d i ∈ FonD AI K LL io T) ∧
          (∀ z ∈ FonD AI K LL io T, ∃ w : Fin n → WCb l,
            (∀ i, w i ∈ Eur io ∧ ∀ g : ↥(GK K), P.χQ (g : GQ l) = 1 → AI.actWCbHom (g : GQ l) (w i) = w i) ∧
            z = ∑ i, ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] w i : RW LL) • d i) ∧
          (∀ z ∈ EurT LL io T, ∃ w : Fin n → WCb l, (∀ i, w i ∈ Eur io) ∧
            z = ∑ i, ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] w i : RW LL) • d i) ∧
          Function.Bijective fun w : Fin n → WCb l =>
            ∑ i, ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] w i : RW LL) • d i) ∧
      ((∃ m : ℕ, K.1 ≤ Ks K m) → ∀ x : WCb l,
        (x ∈ Eur io ∧ ∀ g : ↥(GK K), P.χQ (g : GQ l) = 1 → AI.actWCbHom (g : GQ l) x = x) ↔
          ∃ (n : ℕ) (a : Fin n → WCb l) (xb : Fin n → OCb l), (∀ i, a i ∈ E0 io) ∧
            (∀ i, ∃ (c : ↥(K0 K)) (m : ℕ), 0 < m ∧ ¬ l ∣ m ∧ (c : Om l) ^ m = 1 ∧
              IsTiltOf (c : Om l) m (xb i)) ∧
            x = ∑ i, a i * inclW l (WittVector.teichmuller l (xb i)))

end GlobalTheory.Published
end
end

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NormalCompletionSt
set_option autoImplicit false

namespace GlobalTheory.Published

def NormalCompletionSt : Prop :=
  ∀ (V B : Type) [CommRing V] [IsDedekindDomain V] [CharZero V] [CommRing B] [IsLocalRing B] [IsDomain B]
    [IsIntegrallyClosed B] [Algebra V B] [Algebra.EssFiniteType V B],
    IsDomain (AdicCompletion (IsLocalRing.maximalIdeal B) B) ∧
      IsIntegrallyClosed (AdicCompletion (IsLocalRing.maximalIdeal B) B)

end GlobalTheory.Published
end
