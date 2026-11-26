module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameL

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.IsPairLevel
noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.Bc.ArchbcB.B
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Ex0

def SecEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (S₀ : Finset (Pl E)), S₀.card ≤ 1 →
  ∃ Sec : Set (Pl E), IsSection Sec ∧ (∀ w ∈ S₀, w ∈ Sec) ∧ ∀ w, ¬ IsSplitAt w → w ∈ Sec

def MuEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E →
  ∃ (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e ∧ (∀ w : Pl E, ¬ IsSplitAt w → μ.UnrAt w) ∧ (∀ᶠ w : Pl E in cofinite, μ.UnrAt w) ∧
    ∀ w : Pl E, IsOpen ((μ.loc w).ker : Set (w.adicCompletion E)ˣ)

def UnifEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ w : Pl E,
  ∃ ϖ : (w.adicCompletion E)ˣ, IsUnifAt ϖ ∧ IsUnifV E w (ϖ : w.adicCompletion E)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def IsPairLevel {a b : ℕ} {w : Pl E} (L : Subgroup (GLw a w × GLw b w)) : Prop :=
  ∃ L₁ L₂, L = Subgroup.prod L₁ L₂ ∧ GlobalTheory.BCT.IsLevel (thL a w) (KGL w (n := a)) L₁ ∧ GlobalTheory.BCT.IsLevel (thL b w) (KGL w (n := b)) L₂

def SplitEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E), IsSplitAt w →
  ∀ μ : (w.adicCompletion E)ˣ →* ℂˣ, IsOpen (μ.ker : Set (w.adicCompletion E)ˣ) → ∀ m : ℕ, 1 ≤ m → ∀ KB : Subgroup (UL n w), IsCong m KB →
    ∃ (K' : Subgroup (GLw n w)) (X : Finset (GLw n w)) (e : GLw n w → ℂ) (L : ∀ a : ℕ, Subgroup (GLw a w × GLw (n - a) w)),
      K'.subgroupOf (UL n w) = KB ∧ IsOpen (K' : Set (GLw n w)) ∧ K' ≤ KGL w (n := n) ∧
      (∀ k ∈ KGL w (n := n), ∀ k' ∈ K', k * k' * k⁻¹ ∈ K') ∧ (∀ x ∈ X, x ∈ KGL w (n := n)) ∧ (∀ k ∈ KGL w (n := n), ∃! x ∈ X, x⁻¹ * k ∈ K') ∧
      IsHk K' e ∧ ∀ a (ha : a ≤ n), IsPairLevel (L a) ∧ ∀ y ∈ L a, y ∈ leviOf (Nat.add_sub_of_le ha) w K' ∧
        μ (GeneralLinearGroup.det y.1 ^ (n - a) * GeneralLinearGroup.det y.2 ^ a) = 1

def KEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (Sec : Set (Pl E)), IsSection Sec →
  ∀ R : Finset (Pl E), (∀ w ∈ R, w ∈ Sec) → ∀ μ : ∀ w : Pl E, (w.adicCompletion E)ˣ →* ℂˣ,
  (∀ w, IsOpen ((μ w).ker : Set (w.adicCompletion E)ˣ)) → ∀ L : ∀ (a : ℕ) (w : Pl E), Subgroup (GLw a w × GLw (n - a) w),
  (∀ a ≤ n, ∀ w ∈ R, IsPairLevel (L a w)) →
    ∃ K : ∀ w : Pl E, Subgroup (GLw n w), F5.IsLevel K ∧ (∀ w, IsCompact (K w : Set (GLw n w))) ∧
      (∀ w : Pl E, (∀ u ∈ R, u.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E))) → K w = KGL w (n := n)) ∧
      (∀ a (ha : a ≤ n), ∀ w ∈ R, ∀ m X, blk (Nat.add_sub_of_le ha) w m X ∈ K w →
        m ∈ L a w ∧ μ w (GeneralLinearGroup.det m.1 ^ (n - a) * GeneralLinearGroup.det m.2 ^ a) = 1) ∧
      ∀ a (ha : a ≤ n), ∀ w ∈ R, IsSplitAt w → ∀ u, ConjPl w u → ∀ m X, blk (Nat.add_sub_of_le ha) u m X ∈ K u →
        μ u (GeneralLinearGroup.det m.1 ^ (n - a) * GeneralLinearGroup.det m.2 ^ a) = 1 ∧
          ∃ m' ∈ L a w, embW a u m.1 = embT a w m'.1 ∧ embW (n - a) u m.2 = embT (n - a) w m'.2

end PositivityTheory.Rg.BcB.F.Ex0

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SeenTr
noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8
open scoped Classical

namespace PositivityTheory.Rg.BcB.F

def LocData.IsLetter {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (d : LocData E n) (a : ℕ) (ha : a ≤ n)
    (L : LM d.kap a (n - a)) : Prop :=
  d.IsGen a ha L ∨ (∃ L', d.IsGen a ha L' ∧ L = L'.adj) ∨ L = d.betaL a ha ∨ L = d.fixL a

def SeenTr : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : LocData E n), d.Ok → ∀ a (ha : a ≤ n)
  (ls : List (LM d.kap a (n - a))) (N : ∀ w, d.kap w → d.kap w → ℂ), (∀ L ∈ ls, d.IsLetter a ha L) → ∀ w ∈ d.B,
    (ls.foldr LM.mul (d.eL a)).t w = idem (d.lev₂ a w) ∧
    ((w ∈ d.T → ¬ GlobalTheory.UnitaryBC.IsSplitAt w) →
      seen ((ls.foldr LM.mul (d.eL a)).tr d.P N) (ls.foldr LM.mul (d.eL a)).t w = (ls.foldr LM.mul (d.eL a)).tr d.P N w)

end PositivityTheory.Rg.BcB.F

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.MatchB
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.MB

open PositivityTheory.Rg.BcB.F.U (lpow lone)
open PositivityTheory.Rg.BcN.F2 (mconv)
open PositivityTheory.Rg.BcB.F.MT (MatchLin)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def congK (m : ℕ) (w : Pl E) (k : ℕ) : Set (GLw m w) :=
  {g | g ∈ GlobalTheory.LFun.KGL w (n := m) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤
    WithZero.exp (-(k : ℤ))}

def pairIndicatorMatch (_n a b : ℕ) (w : Pl E) (k : ℕ) (y : GLw a w × GLw b w) : ℂ :=
  ((-((Real.sqrt (qV E w : ℝ) : ℝ) : ℂ)) ^ (k * a * b))⁻¹ *
    (if y.1 ∈ GlobalTheory.LFun.KGL w (n := a) ∧ nrmL a w y.1 ∈ congK a w k ∧ y.2 ∈ GlobalTheory.LFun.KGL w (n := b) ∧ nrmL b w y.2 ∈ congK b w k then 1
      else 0)

def LponeIdem : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (K' : Subgroup (UL n w)),
    IsLevel (MonoidHom.id _) (KL n w) K' → ∀ m : ℕ, lpow K' (lone K') m = lone K'

def FixIdem : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (L : Subgroup (GLw a w × GLw b w)),
    IsOpen (L : Set (GLw a w × GLw b w)) → L ≤ (GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b)) →
    ∀ φ : GLw a w × GLw b w → ℂ, IsHecke L φ → mconv φ (idem L) = φ ∧ mconv (idem L) φ = φ

def MatchBadS : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a : ℕ) (ha : a ≤ n) (w : Pl E), IsSplitAt w →
    ∀ (μ : (w.adicCompletion E)ˣ →* ℂˣ) (K' : Subgroup (UL n w)), IsLevel (MonoidHom.id _) (KL n w) K' → ∀ m : ℕ,
      Match n a (n - a) w μ (lpow K' (lone K') m) (ctMu (Nat.add_sub_cancel' ha) w μ (lone K'))

def MatchBadI : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ w : Pl E, ¬ IsSplitAt w → ∀ (n a b k : ℕ), a + b = n →
    1 ≤ k → ∀ K' : Subgroup (UL n w), IsLevel (MonoidHom.id _) (KL n w) K' → (∀ γ : UL n w, γ ∈ K' ↔ γ.1 ∈ congK n w k) →
      ∀ m : ℕ, Match n a b w 1 (lpow K' (lone K') m) (fun y => ((K'.relIndex (KL n w) : ℕ) : ℂ) * pairIndicatorMatch n a b w k y)

def MatchUnitI : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ w : Pl E, ¬ IsSplitAt w → ∀ n a : ℕ, a ≤ n →
    Match n a (n - a) w 1 ((KL n w : Set (UL n w)).indicator 1) (idem (K2 a (n - a) w))

def MatchBadSOf : Prop := M3 → LponeIdem → MatchBadS
def MatchUnitIOf : Prop := M1 → MatchUnitI

end PositivityTheory.Rg.BcB.F.MB

end
end
