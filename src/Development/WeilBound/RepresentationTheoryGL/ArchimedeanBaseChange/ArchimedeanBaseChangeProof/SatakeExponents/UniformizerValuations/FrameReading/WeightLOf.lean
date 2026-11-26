module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameA
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameL

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FGLeaf
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F.FG

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def ConjFix : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ),
  (∀ (w u : Pl E) (G : H E a b → ℂ), IsSplitAt w → ConjPl w u → G ∈ fixed (pairRtT a b w) (K2 a b w) →
    G ∈ fixed (pairRt a b u) (K2 a b u)) ∧
  ∀ S : Set (Pl E), IsSection S → (∀ u, IsSplitAt u → u ∈ S ∨ ∃ w ∈ S, IsSplitAt w ∧ ConjPl w u) ∧
    ∀ X : Finset (Pl E), {u | ∃ w ∈ X, ConjPl w u}.Finite

def USat : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)) (w : Pl E)
  (σ : SmIrr (UL n w)), IsSplitAt w → IsCompU π w σ → fixed σ.ρ (KL n w) ≠ ⊥ →
  ∃ B, SatAtU π w B ∧ ∀ ϖ, IsUnifV E w ϖ → ∀ k ≤ n,
    twTr σ.ρ (KL n w) (KL n w) (fun u => Tj ℂ n (Ov E w) ϖ k u.1) LinearMap.id = satEig (qV E w) n B k

def CtHecke : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E)
  (ν : (w.adicCompletion E)ˣ →* ℂˣ) (ϖ : w.adicCompletion E) (k : ℕ), IsSplitAt w → IsUnifV E w ϖ →
  (∀ u : (w.adicCompletion E)ˣ, ordL (u : w.adicCompletion E) = 0 → ν u = 1) →
  HasCompactSupport (ctT h w ν ϖ k) ∧ (∀ y ∈ K2 a b w, ∀ g, ctT h w ν ϖ k (g * y) = ctT h w ν ϖ k g) ∧ ν ((-1) ^ (a * b)) = 1

def USatOf : Prop := SplitDict → USat

end PositivityTheory.Rg.BcB.F.FG

end
end

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F.FG

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def GoodL : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (n a : ℕ) (ha : a ≤ n)
  (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π → ∀ (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e →
  ∀ (Sec : Set (Pl E)), IsSection Sec → ∀ d : LocData E n, d.Ok → (↑d.P : Set (Pl E)) ⊆ Sec → (∀ w, d.μ w = μ.loc w) →
  (∀ w, IsUnifV E w (d.ϖ w : w.adicCompletion E)) → (∀ w ∈ Sec, w ∉ d.S₀ → w ∉ d.Bad → μ.UnrAt w) →
  ∀ (σ : ∀ w : Pl E, SmIrr (UL n w)), (∀ w ∈ Sec, IsCompU π w (σ w) ∧ fixed (σ w).ρ (d.KU w) ≠ ⊥) →
  ∀ (l₁ : InfinitePlace E → DomWeight a) (l₂ : InfinitePlace E → DomWeight (n - a)) (μ₁ : Measure (GA E a))
    (μ₂ : Measure (GA E (n - a))) (μa : Measure (PositivityTheory.RgTw.G a)) (μb : Measure (PositivityTheory.RgTw.G (n - a)))
    (A : Arch E a (n - a) l₁ l₂ μ₁ μ₂ μa μb) (s₁ : Tr E a) (s₂ : Tr E (n - a)) (Pa : Pre E a) (Pb : Pre E (n - a)) (D : Pre E n),
  Ctx μ s₁ s₂ Pa Pb D → IsLev (d.lev a) → IsLev (d.lev₂ a) →
  ∀ (I : Type) (G : I × (∀ w : d.P, d.kap w) → H E a (n - a) → ℂ), G ≠ 0 →
  (∀ j, G j ∈ pairSpace s₁.space s₂.space) → (∀ j, OfLev Sec (d.lev a) (d.lev₂ a) (G j)) →
  (∀ w ∈ Sec, d.Good w → ∀ (k : ℕ) (intersection_update_fsHerm_neg_one : Bool),
    convF A.ν (fm Sec d.P (A.blk (∀ w : d.P, d.kap w)) (Equiv.refl _) (d.hL a ha w k intersection_update_fsHerm_neg_one)) G =
      twTr (σ w).ρ (KL n w) (KL n w) (d.hU w k) LinearMap.id • G) →
  ∀ᶠ w : Pl E in cofinite, IsSplitAt w → D.SplitAt π w

def WeightL : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e →
  ∀ (lam : InfinitePlace E → DomWeight n), (∀ v, HasWeightAt π v.embedding (lam v)) → ∀ (a b : ℕ)
    (l₁ : InfinitePlace E → DomWeight a) (l₂ : InfinitePlace E → DomWeight b),
  (∀ v, (infOfWeight (l₁ v)).map (· + (b : ℂ) * (e v : ℂ) / 2) + (infOfWeight (l₂ v)).map (· + (a : ℂ) * (e v : ℂ) / 2) =
    infOfWeight (lam v)) →
  ∀ (s₁ : Tr E a) (s₂ : Tr E b) (Pa : Pre E a) (Pb : Pre E b) (D : Pre E n), Ctx μ s₁ s₂ Pa Pb D →
  (∀ τ, HasInfCharGL s₁.space τ (mOf (fun v => PositivityTheory.RgBcC.infOf (l₁ v).w) τ)) →
  (∀ τ, HasInfCharGL s₂.space τ (mOf (fun v => PositivityTheory.RgBcC.infOf (l₂ v).w) τ)) →
  (∃ G ∈ pairSpace s₁.space s₂.space, G ≠ 0) → ∀ τ lam', HasWeightAt π τ lam' → ∑ j, D.m j τ = infOfWeight lam'

def GoodLOf : Prop := ReadSplit → FmOne → ActHecke → LocOk → ConjFix → USat → CtHecke → GoodL

def WeightLOf : Prop := InfTree → gamma_zeta_nabla_cancel.RegDom → JoinInf → TreeInf → WeightJoin → WeightL

end PositivityTheory.Rg.BcB.F.FG

end
