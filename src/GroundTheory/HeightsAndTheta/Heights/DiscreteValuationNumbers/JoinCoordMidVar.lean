module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SpanTwoIsPrimeRelevant
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.JoinCoordMidVar
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

variable {K K' K₂ : Type} {ι : K → Type} {ι' : K' → Type}

def midDeg (a : K ⊕ K' → ℤ) : K ⊕ (K₂ ⊕ K') → ℤ :=
  Sum.elim (fun k => a (.inl k)) (Sum.elim 0 (fun k => a (.inr k)))

def midVar (ι₂ : K₂ → Type) :
    (Σ k : K ⊕ K', Sum.elim ι ι' k) → (Σ k : K ⊕ (K₂ ⊕ K'), Sum.elim ι (Sum.elim ι₂ ι') k)
  | ⟨.inl k, i⟩ => ⟨.inl k, i⟩
  | ⟨.inr k, i⟩ => ⟨.inr (.inr k), i⟩

theorem joinCoord_midVar {Ω : Type*} (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) {ι₂ : K₂ → Type}
    (w : (Σ k, ι₂ k) → Ω) (p : Σ k : K ⊕ K', Sum.elim ι ι' k) :
    joinCoord x (joinCoord w z) (midVar ι₂ p) = joinCoord x z p := by
  obtain ⟨k | k, i⟩ := p <;> rfl

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.DivisorIdealBotUniformiser
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Defs

variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]

def divisorIdeal (P : Ideal (MRing ι R)) (f g : MRing ι R) : Ideal (MRing ι R) :=
  (P ⊔ Ideal.span {f}).colon {g}

end Defs

section Lemmas

def VNumCut.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (G : Ideal (MRing ι O)) (n : ℕ), G.IsPrime → IsMultiHomogIdeal G → (C ϖ : MRing ι O) ∈ G →
    ringKrullDim (MRing ι O ⧸ G) < ((n + 2 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ (s : MRing ι O) (c : K → ℕ), IsMultiHomog s c → s ∉ G →
    ∀ bs : Fin n → K → ℤ,
      vNum G (Matrix.vecCons (fun k => (c k : ℤ)) bs) = cycEval (fun U => vNum U bs) (divCycle G s)

def DivisorIdealCycle.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (K : Type) [Fintype K] [DecidableEq K]
    (ι : K → Type) [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι R)) (f g u v : MRing ι R),
    P.IsPrime → W.IsPrime → P ≤ W → g ∉ P →
    (∀ U : Ideal (MRing ι R), U.IsPrime → W ≤ U → IsRelevant U →
      ∃ u' v' : MRing ι R, u' ∉ U ∧ u' * f - v' * g ∈ P) →
    u ∉ W → v ∉ W → u * f - v * g ∈ P →
    ratDiv W v u = idealCycle (W ⊔ divisorIdeal P f g)

def VertCutEff.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (n : ℕ), IsModelOver P (n + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsEffectiveVertical P ϖ b f g →
    ∀ (W : Ideal (MRing ι O)) (x : MRing ι O), x ∉ P → W ∈ (P ⊔ Ideal.span {x}).minimalPrimes →
      IsRelevant W → IsMultiHomogIdeal W → (C ϖ : MRing ι O) ∈ W → ratDiv P f g W = 0 →
    ∀ L : Fin n → K → ℤ,
      vNum W (Matrix.vecCons b L) =
        cycEval (fun U => vNum U L) (idealCycle (W ⊔ divisorIdeal P f g))

def LeftExpansion.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsVerticalDivisor P ϖ b f g →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
    (∀ G, (C ϖ : MRing ι O) ∈ G → divCycle P s G ≠ 0 → ratDiv P f g G = 0) →
    ∀ L : Fin d → K → ℤ,
      cycEval (fun G => vNum G (Matrix.vecCons (fun k => (c k : ℤ)) L)) (ratDiv P f g) =
        cycEval (fun U => vNum U L) (fun U => cycEval (fun G => divCycle G s U) (ratDiv P f g))


open Classical in
def RightExpansion.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsEffectiveVertical P ϖ b f g →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g) →
    (∀ G, (C ϖ : MRing ι O) ∈ G → divCycle P s G ≠ 0 → ratDiv P f g G = 0) →
    ∀ L : Fin d → K → ℤ,
      cycEval (fun W => if (C ϖ : MRing ι O) ∈ W then vNum W (Matrix.vecCons b L)
          else cycEval (fun G => vNum G L) (ratDiv W f g)) (divCycle P s) =
        cycEval (fun U => vNum U L)
          (fun U => cycEval (fun W => idealCycle (W ⊔ divisorIdeal P f g) U) (divCycle P s))

def LocalCoefficient.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsEffectiveVertical P ϖ b f g →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g) →
    (∀ G, (C ϖ : MRing ι O) ∈ G → divCycle P s G ≠ 0 → ratDiv P f g G = 0) →
    ∀ U : Ideal (MRing ι O),
      (U.IsPrime → IsMultiHomogIdeal U → IsRelevant U → (C ϖ : MRing ι O) ∈ U →
        ((d + Fintype.card K : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι O ⧸ U)) →
      cycEval (fun G => divCycle G s U) (ratDiv P f g) =
        cycEval (fun W => idealCycle (W ⊔ divisorIdeal P f g) U) (divCycle P s)

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTerSide
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (IsModelOver mcIdeal joinCoord fnField)

def JoinTwoModels.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (d : ℕ), IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d →
    ∀ (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)] (z₁ : (Σ k, ι₁ k) → Ω)
      (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)] (z₂ : (Σ k, ι₂ k) → Ω),
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z₁)) d → fnField O (joinCoord x z₁) = fnField O x →
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z₂)) d → fnField O (joinCoord x z₂) = fnField O x →
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x (joinCoord z₁ z₂))) d ∧
        fnField O (joinCoord x (joinCoord z₁ z₂)) = fnField O x

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsBisRest
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)

universe u v w

def FlagPairCharacterisation.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type v) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (N : ℕ) (E : Type w) [AddCommGroup E] [Module Ω E]
    (B B' : ChartBundle O (segreVec y) N E) (ϖ : O), Irreducible ϖ →
    IsMultiProjPrime (pointIdeal O y) →
    (∀ (w w' : Module.Basis (Fin N) Ω E) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g ↔
        ∃ F : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagPair O y B B', F.gen = w ∧ F.gen' = w' ∧ F.deg = x ∧
          F.deg' = x' ∧ F.f = f ∧ F.g = g) ∧
    ((∃ c, segreVec y c ≠ 0) → ∀ F : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagPair O y B B',
      LinearIndependent Ω F.gen ∧ LinearIndependent Ω F.gen')

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Inhabit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)

def ChernClassOnFlagPair.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
      [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (d : ℕ), Nonempty K →
      IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E] (B B' : ChartBundle O (segreVec y) N E),
      SameGenericFibre ϖ B B' →
    ∀ (w w' : Module.Basis (Fin N) Ω E) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g →
    (∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ Gs : Fin N → MvPolynomial (Fin N ⊕ Fin N) ℤ,
      IsPairExpansion k (psum (Fin N) ℤ k) Gs →
      ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - k) →
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ck O y d N B B' k L Q =
          ∑ μ ∈ Q.support, Q.coeff μ * pairNum (pointIdeal O y) x x' f g Gs (classList L μ)) ∧
    (∀ (c : ℕ) (G : MvPolynomial (Fin N) ℤ), G.IsSymmetric → G.IsHomogeneous c → c ≤ d →
      ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d - c) →
      ∀ a : O, a ≠ 0 →
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.rootNum O y d N B G L Q a =
          ∑ μ ∈ Q.support, Q.coeff μ *
            cycEval (fun W => classNum x G (classList L μ) W) (divCycle (pointIdeal O y) (C a)))

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.TrivBundleIsTwistedForms
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR

open MvPolynomial Module ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

universe u v w u₁ u₂

section Coordinates

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {o : Type*} [CommRing o] {Ω : Type*} [Field Ω] [Algebra o Ω]

def segreVec (pt : MRingOver o ι →ₐ[o] Ω) : ((k : K) → ι k) → Ω :=
  fun i => ∏ k, pt (X ⟨k, i k⟩)

end Coordinates

section Flags

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {o : Type*} [CommRing o] {Ω : Type*} [Field Ω] [Algebra o Ω]
variable {E : Type*} [AddCommGroup E] [Module Ω E] {N : ℕ}

end Flags

section ProjBundle

variable {K : Type*} [Fintype K]

variable {ι : K → Type w} [∀ k, Fintype (ι k)] {τ : Type w} [Fintype τ]
variable {F : Type*} [Field F] {Ω : Type*} [Field Ω] [Algebra F Ω]
variable {E : Type*} [AddCommGroup E] [Module Ω E] {N : ℕ}

end ProjBundle

section PolyNum

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def monoList {N : ℕ} (mono : Fin N →₀ ℕ) : List (Fin N) :=
  (List.finRange N).flatMap fun l => List.replicate (mono l) l

def tupleOfList {α : Type*} [Zero α] {n : ℕ} (L : List α) : Fin n → α := fun j => L.getD j 0

variable {F : Type*} [Field F]

def polyNum (I : IFamily F ι) (V : Ideal (MRingOver F ι)) (n : ℕ) {N : ℕ} (cls : Fin N → K → ℤ)
    (Q : MvPolynomial (Fin N) ℤ) (Y : List (K → ℤ)) : ℤ :=
  ∑ mono ∈ Q.support, Q.coeff mono * I V n (tupleOfList ((monoList mono).map cls ++ Y))

end PolyNum

section Pairs

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

structure VPair (K : Type*) [Fintype K] (O : Type*) [CommRing O] (ι : K → Type*) [∀ k, Fintype (ι k)] where

  y : K → ℤ

  b : K → ℤ

  f : MRingOver O ι

  g : MRingOver O ι

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def vNum (P : Ideal (MRingOver O ι)) (Iκ : IFamily (IsLocalRing.ResidueField O) ι) (n : ℕ)
    (p : VPair K O ι) (L : List (K → ℤ)) : ℤ :=
  redEval (fun W => Iκ W n (tupleOfList L)) (divO P p.f p.g)

def monoPairNum (P : Ideal (MRingOver O ι)) (Iκ : IFamily (IsLocalRing.ResidueField O) ι) (n : ℕ)
    {r : ℕ} (pr : Fin r → VPair K O ι) (ls : List (Fin r)) : ℤ :=
  ∑ k : Fin ls.length, vNum P Iκ n (pr (ls.get k))
    ((ls.take k).map (fun l => (pr l).y - (pr l).b) ++ (ls.drop (k + 1)).map fun l => (pr l).y)

def pairNum (P : Ideal (MRingOver O ι)) (Iκ : IFamily (IsLocalRing.ResidueField O) ι) (n : ℕ)
    {r : ℕ} (pr : Fin r → VPair K O ι) (Q : MvPolynomial (Fin r) ℤ) : ℤ :=
  ∑ mono ∈ Q.support, Q.coeff mono * monoPairNum P Iκ n pr (monoList mono)

variable {Ω : Type*} [Field Ω] [Algebra O Ω] {E : Type*} [AddCommGroup E] [Module Ω E] {N : ℕ}

end Pairs

section Inhabitants

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable (o : Type*) [CommRing o] {Ω : Type*} [Field Ω] [Algebra o Ω]

variable {o}





variable (o) in
def genPt (R : Type*) [CommRing R] [IsDomain R] (ι : K → Type*) [∀ k, Fintype (ι k)] :
    MRingOver R ι →ₐ[R] FractionRing (MRingOver R ι) :=
  IsScalarTower.toAlgHom R _ _


section DVR

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

end DVR

end Inhabitants

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsBisTer
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

def dividedDifferenceExpansion.Statement : Prop :=
  ∀ (r m : ℕ) (G : MvPolynomial (Fin r) ℤ), G.IsHomogeneous m →
    IsPairExpansion m G
      (fun l => rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff l G))

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InhabitLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (joinCoord fnField)

def BirationalJoin.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
    (w : (Σ k, ι₂ k) → Ω),
    fnField O (joinCoord y w) = fnField O y → IsBirationalJoin O y w

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsConeTrdegFnField
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mcIdeal fnField)

def ConeTrdegFnField.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] (Ω : Type) [Field Ω] [Algebra O Ω],
    Function.Injective (algebraMap O Ω) →
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω),
      (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) →
      Algebra.trdeg O (MRingOver O ι ⧸ mcIdeal O y) =
        Algebra.trdeg O (Algebra.adjoin O (fnField O y : Set Ω)) + Fintype.card K

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsPointIdealMultiProj
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

def PointIdealMultiProj.Statement : Prop :=
  ∀ (F : Type) [Field F] (L : Type) [Field L] [Algebra F L]
    (K : Type) [DecidableEq K] (ι : K → Type) (z : (Σ k, ι k) → L),
    (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → IsMultiProjPrime (pointIdeal F z)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InhabitMore
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

def plainPolynomialPairNumber.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K]
    [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d N : ℕ)
    (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O) (m : ℕ) (G : MvPolynomial (Fin N) ℤ),
    G.IsHomogeneous m → m ≤ d + 1 →
    ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - m) →
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O (fun V _ bs => intNum (IsLocalRing.ResidueField O) V bs) P d
                                (Fin.append x L) (Fin.append x' L) (Fin.append f fun _ => 1) (Fin.append g fun _ => 1)
                                (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q) =
        ∑ μ ∈ Q.support, Q.coeff μ * pairNum P x x' f g
          (fun i => rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff i G)) (classList L μ)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InhabitFurther
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

def RootPolynomialNumber.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K]
    [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d N : ℕ)
    (x : Fin N → K → ℤ) (c : ℕ) (G : MvPolynomial (Fin N) ℤ), G.IsHomogeneous c → c ≤ d →
    ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d - c) →
    ∀ a : O,
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O (fun W => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
                                (fun V _ bs => intNum (IsLocalRing.ResidueField O) V bs) W d (Fin.append x L)
                                (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q))
        (Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P (C a))) =
      ∑ μ ∈ Q.support, Q.coeff μ * cycEval (fun W => classNum x G (classList L μ) W) (divCycle P (C a))

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsTwistedDualGensSpan
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def TwistedDualGensSpan.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (Ω : Type) [Field Ω] [Algebra R Ω]
    (K : Type) [Fintype K] (ι : K → Type) (y : (Σ k, ι k) → Ω)
    (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E] (B : ChartBundle R (segreVec y) N E)
    (a : K → ℤ) (M : ℕ) (φ : Fin M → Module.Dual Ω E),
    IsTwistedDualGens y B a φ → ∀ c, segreVec y c ≠ 0 →
      Submodule.span Ω (Set.range φ) = ⊤

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsVerticalDivisorJoinPullback
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

def VerticalDivisorJoinPullback.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O)
    (Ω : Type) [Field Ω] [Algebra O Ω]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω) (b : K → ℤ) (f g : MRing ι O),
    IsVerticalDivisor (pointIdeal O y) ϖ b f g →
      IsVerticalDivisor (pointIdeal O (joinCoords y y')) ϖ (joinDeg b) (joinForm f) (joinForm g)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PIntNumIsFieldIntersection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

private theorem isMultiProjPrime_of_vocab (h2 : VocabMultiHomogIdeal.Statement.{u})
    {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {V : Ideal (MRing ι F)}
    (hV : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime V) : IsMultiProjPrime V :=
  ⟨hV.1, (h2 F K ι V).1 hV.2.1, hV.2.2⟩

private theorem finsum_mul_eq_finsupp_sum {α : Type*} (D : α →₀ ℤ) (J : α → ℤ) :
    ∑ᶠ W, D W * J W = D.sum fun W m => m * J W := by
  classical
  rw [Finsupp.sum, finsum_eq_sum_of_support_subset]
  intro W hW
  rw [Function.mem_support] at hW
  rw [Finset.mem_coe, Finsupp.mem_support_iff]
  intro h0
  exact hW (by rw [h0, zero_mul])

theorem IntNumIsFieldIntersection.proof (h1 : VocabMultiHomog.Statement.{u})
    (h2 : VocabMultiHomogIdeal.Statement.{u}) (h3 : VocabDivCycle.Statement.{u})
    (h4 : IntNumPoint.Statement.{u}) (h5 : IntNumRatSection.Statement.{u}) :
    IntNumIsFieldIntersection.Statement.{u} := by
  intro F _ K _ _ ι _
  refine ⟨?_, ?_⟩
  · intro V L i hV hi
    have hL : L = (![] : Fin 0 → K → ℤ) := funext fun j => Fin.elim0 j
    subst hL
    exact h4 F K ι V i (isMultiProjPrime_of_vocab h2 hV.1) hV.2 hi
  · intro V n L A f g hV hs
    obtain ⟨α, β, hf, hg, hfV, hgV, hαβ⟩ := hs
    have key := h5 F K ι n V (isMultiProjPrime_of_vocab h2 hV.1) hV.2 L A f g α β
      ((h1 F K ι f α).1 hf) ((h1 F K ι g β).1 hg) hfV hgV hαβ
    refine key.trans ?_
    have hD : ∀ W, ratDiv V f g W = ReciprocityTheory.ChartRestriction.G.AI.I1.ratDiv V f g W := by
      intro W
      simp only [ratDiv, ReciprocityTheory.ChartRestriction.G.AI.I1.ratDiv, Finsupp.sub_apply, Finsupp.mapRange_apply]
      rw [h3 F K ι V f W, h3 F K ι V g W]
    simp only [cycEval, ReciprocityTheory.ChartRestriction.G.AI.I1.cycEval, hD]
    exact finsum_mul_eq_finsupp_sum _ _

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
