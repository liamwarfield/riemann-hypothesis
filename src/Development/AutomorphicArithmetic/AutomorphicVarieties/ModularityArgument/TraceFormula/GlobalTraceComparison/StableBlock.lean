module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.IsTransl
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.BindPow
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8 (K2)
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison

inductive Ex (ι : Type) : Type
  | one : Ex ι
  | gen : ι → Ex ι
  | smul : ℂ → Ex ι → Ex ι
  | add : Ex ι → Ex ι → Ex ι
  | mul : Ex ι → Ex ι → Ex ι

namespace Ex

variable {ι κ : Type}

def ev (x : ι → ℂ) : Ex ι → ℂ
  | one => 1
  | gen i => x i
  | smul c a => c * a.ev x
  | add a b => a.ev x + b.ev x
  | mul a b => a.ev x * b.ev x

def pow (e : Ex ι) : ℕ → Ex ι
  | 0 => one
  | k + 1 => mul (e.pow k) e

def bind (τ : ι → Ex κ) : Ex ι → Ex κ
  | one => one
  | gen i => τ i
  | smul c a => smul c (a.bind τ)
  | add a b => add (a.bind τ) (b.bind τ)
  | mul a b => mul (a.bind τ) (b.bind τ)

theorem ev_pow (x : ι → ℂ) (e : Ex ι) (k : ℕ) : (e.pow k).ev x = e.ev x ^ k := by
  induction k with
  | zero => simp [pow, ev]
  | succ k ih => simp [pow, ev, ih, pow_succ]

theorem bind_pow (τ : ι → Ex κ) (e : Ex ι) (k : ℕ) : (e.pow k).bind τ = (e.bind τ).pow k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [pow, bind, ih]

def fn {G : Type} [Group G] (K : Subgroup G) (g : ι → G → ℂ) : Ex ι → G → ℂ
  | one => (K : Set G).indicator 1
  | gen i => g i
  | smul c a => fun y => c * a.fn K g y
  | add a b => fun y => a.fn K g y + b.fn K g y
  | mul a b => fun y => hint K fun z => a.fn K g z * b.fn K g (z⁻¹ * y)

end Ex

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n a b : ℕ}

def unif (w : Pl E) : w.adicCompletion E := Classical.epsilon (IsUnifV E w)

def fn1 (n : ℕ) (w : Pl E) (e : Ex (Fin (n + 1))) : GLw n w → ℂ :=
  e.fn (KGL w (n := n)) fun j : Fin (n + 1) => Tj ℂ n (Ov E w) (unif w) j

def ev1 (n : ℕ) (w : Pl E) (e : Ex (Fin (n + 1))) (B : Multiset ℂˣ) : ℂ := e.ev fun j : Fin (n + 1) => satEig (qV E w) n B j

def fn2 (a b : ℕ) (w : Pl E) (e : Ex (Fin (a + 1) × Fin (b + 1))) : GLw a w × GLw b w → ℂ :=
  e.fn (K2 a b w) fun p y => Tj ℂ a (Ov E w) (unif w) p.1 y.1 * Tj ℂ b (Ov E w) (unif w) p.2 y.2

def ev2 (a b : ℕ) (w : Pl E) (e : Ex (Fin (a + 1) × Fin (b + 1))) (B₁ B₂ : Multiset ℂˣ) : ℂ :=
  e.ev fun p => satEig (qV E w) a B₁ p.1 * satEig (qV E w) b B₂ p.2

def inv (B : Multiset ℂˣ) : Multiset ℂˣ := B.map (·⁻¹)

structure CD (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) where
  c : ℕ
  N : Fin c → ℕ
  P : ∀ i, CG E (N i)
  pos : ∀ i, 1 ≤ N i
  sum : ∑ i, N i = n

def CD.nil (E : Type) [Field E] [NumberField E] [IsCMField E] : CD E 0 := ⟨0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, rfl⟩

def CD.Sat (D : CD E n) (w : Pl E) (B : Multiset ℂˣ) : Prop :=
  ∃ b : Fin D.c → Multiset ℂˣ, (∀ i, (D.P i).HasSat w (b i)) ∧ ∑ i, b i = B

def CD.Has {m : ℕ} (D : CD E n) (π : CuspSub E m) : Prop := ∃ i, (⟨D.N i, D.P i⟩ : Σ k, CG E k) = ⟨m, CG.mk π⟩

def Off (Z : Finset (Pl E)) (w : Pl E) : Prop := w ∉ Z ∧ cPl w ∉ Z

def SplitIn (S : Set (Pl E)) (Z : Finset (Pl E)) : Prop := ∀ w ∈ Z, w ∈ S ∧ IsSplitAt w

def Lc {G : Type} [Group G] [TopologicalSpace G] (K : Subgroup G) (f : G → ℂ) : Prop :=
  ∃ K' : Subgroup G, IsOpen (K' : Set G) ∧ K' ≤ K ∧ IsHecke K' f

def trc {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G) (f : G → ℂ) : ℂ :=
  twTr ρ K (K ⊓ rStab f ⊓ rStab fun y => f y⁻¹) f LinearMap.id

def fam (Z T : Finset (Pl E)) (φ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) (e₁ e₂ : Pl E → Ex (Fin (a + 1) × Fin (b + 1)))
    (k : ℕ) (w : Pl E) : GLw a w × GLw b w → ℂ :=
  if w ∈ Z then φ w else if w ∈ T then fn2 a b w (((e₁ w).pow k).mul ((e₂ w).pow k)) else (K2 a b w : Set _).indicator 1

def val (T : Finset (Pl E)) (e₁ e₂ : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) (B₁ B₂ : Pl E → Multiset ℂˣ) : ℂ :=
  ∏ w ∈ T, ev2 a b w (e₁ w) (B₁ w) (B₂ w) * ev2 a b w (e₂ w) (inv (B₁ (cPl w))) (inv (B₂ (cPl w)))

def Small (ρ : ℝ) (x : ℕ → ℂ) : Prop := ∃ (C : ℝ) (N : ℕ), ∀ k, ‖x k‖ ≤ C * (1 + k) ^ N * ρ ^ k

end UpperTheory.V.Z.Tf.GlobalTraceComparison
end
end

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison

def RunC : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : CuspSub E n,
  (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.DualIsConj π → (∀ w, ¬ IsSplitAt w → ∃ B, (CG.mk π).HasSat w B) →
    (∃ σ : Submodule ℂ (UA E n → ℂ), IsAutRepU σ ∧ (∀ w : Pl E, ¬ IsSplitAt w → IsUnramU σ w) ∧
      ∀ᶠ w : Pl E in cofinite, IsSplitAt w → ∃ (τ : SmIrr (GLw n w)) (B : Multiset ℂˣ),
        IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ ∧ HasSatGL w τ.ρ B ∧ (CG.mk π).HasSat w B) ∨
    ∃ D : CD E n, ¬ D.Has π ∧ ∀ᶠ w : Pl E in cofinite, IsSplitAt w → ∃ B, D.Sat w B ∧ (CG.mk π).HasSat w B

def G2s : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e →
  ∀ lam : InfinitePlace E → DomWeight n, ∃ (ι : Type) (_ : Fintype ι) (a : ι → ℕ) (l₁ : ∀ i, InfinitePlace E → DomWeight (a i))
    (l₂ : ∀ i, InfinitePlace E → DomWeight (n - a i)) (sg : ι → ℤˣ),
    (∀ i, a i ≤ n ∧ ∀ v, (infOfWeight (l₁ i v)).map (· + ((n - a i : ℕ) : ℂ) * (e v : ℂ) / 2) +
      (infOfWeight (l₂ i v)).map (· + (a i : ℂ) * (e v : ℂ) / 2) = infOfWeight (lam v)) ∧
    (∃ i, a i = n ∧ sg i = 1 ∧ ∀ j, a j = n → j = i) ∧ (∃ i, a i = 0 ∧ sg i = 1 ∧ ∀ j, a j = 0 → j = i) ∧
    ∀ S : Set (Pl E), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ)
      (φ : ∀ a (w : Pl E), GLw a w × GLw (n - a) w → ℂ), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' →
      GlobalTheory.BCT.IsTest (KL n) K' f → (∀ a ≤ n, IsTestP (φ a) ∧ ∀ w ∈ S, Match n a (n - a) w (μ.loc w) (f w) (φ a w)) →
      geomU S lam f = ∑ i, ((sg i : ℤ) : ℂ) * geomSt2 S (l₁ i) (l₂ i) (φ (a i))

def MuEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∃ (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e

def MatchUnit : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ w : Pl E, ¬ IsSplitAt w → ∀ n a b : ℕ, a + b = n →
  Match n a b w 1 ((KL n w : Set (UL n w)).indicator 1) ((K2 a b w : Set _).indicator 1)

def MatchSplit : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), IsSplitAt w → ∀ (n a b : ℕ) (h : a + b = n) (μ : HChar E) (f : UL n w → ℂ),
  Lc (KL n w) f → Lc (K2 a b w) (ctMu h w (μ.loc w) f) ∧ Match n a b w (μ.loc w) f (ctMu h w (μ.loc w) f)

def EndoBlock : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (a b : ℕ), 1 ≤ a + b → ∀ S : Set (Pl E), IsSection S →
  ∀ (l₁ : InfinitePlace E → DomWeight a) (l₂ : InfinitePlace E → DomWeight b) (Z : Finset (Pl E)), SplitIn S Z →
    ∀ φ : ∀ w : Pl E, GLw a w × GLw b w → ℂ, (∀ w ∈ Z, Lc (K2 a b w) (φ w)) → (∃ w ∈ Z, RegAt2 a b w (φ w)) →
    ∃ (J : Type) (_ : Fintype J) (D₁ : J → CD E a) (D₂ : J → CD E b) (B₁ B₂ : J → Pl E → Multiset ℂˣ),
      (∀ j w, Off Z w → (D₁ j).Sat w (B₁ j w) ∧ (D₂ j).Sat w (B₂ j w)) ∧
      ∀ T : Finset (Pl E), SplitIn S T → Disjoint T Z → ∀ (e₁ e₂ : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) (ρ : ℝ), 0 < ρ →
        (∀ j, ‖val T e₁ e₂ (B₁ j) (B₂ j)‖ < ρ) → Small ρ fun k => geomSt2 S l₁ l₂ (fam Z T φ e₁ e₂ k)

def StableBlock : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : CuspSub E n,
  (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.DualIsConj π → ∃ l₁ : InfinitePlace E → DomWeight n,
    ∀ (l₂ : InfinitePlace E → DomWeight 0) (S : Set (Pl E)), IsSection S → ∀ Z : Finset (Pl E), SplitIn S Z →
    ∀ (B : Pl E → Multiset ℂˣ) (τ : ∀ w : Pl E, SmIrr (GLw n w)), (∀ w, Off Z w → (CG.mk π).HasSat w (B w)) →
    (∀ w ∈ Z, π.IsLocComp w (τ w)) → ∃ c : ℂ, c ≠ 0 ∧
    ∀ φ : ∀ w : Pl E, GLw n w × GLw 0 w → ℂ, (∀ w ∈ Z, Lc (K2 n 0 w) (φ w)) → (∃ w ∈ Z, RegAt2 n 0 w (φ w)) →
    ∃ (J : Type) (_ : Fintype J) (D : J → CD E n) (B₁ : J → Pl E → Multiset ℂˣ),
      (∀ j, ¬ (D j).Has π ∧ ∀ w, Off Z w → (D j).Sat w (B₁ j w)) ∧
      ∀ T : Finset (Pl E), SplitIn S T → Disjoint T Z → ∀ (e₁ e₂ : Pl E → Ex (Fin (n + 1) × Fin (0 + 1))) (ρ : ℝ), 0 < ρ →
        (∀ j, ‖val T e₁ e₂ (B₁ j) 0‖ < ρ) → Small ρ fun k => geomSt2 S l₁ l₂ (fam Z T φ e₁ e₂ k) -
          c * (∏ w ∈ Z, trc (τ w).ρ (KGL w (n := n)) fun g => φ w (g, 1)) * val T e₁ e₂ B 0 ^ k

def Peak : Prop := ∀ (B : Type) [CommRing B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B] (H : Type) [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H] (R : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (A : StarSubalgebra ℂ B) (p : A →⋆ₐ[ℂ] ℂ) (a₀ : A) (x : B)
  (ρ : ℝ), p a₀ = 1 → 0 < ρ →
  (∀ s : B →⋆ₐ[ℂ] ℂ, (∀ y, ‖s y‖ ≤ ‖R y‖) → (∀ a : A, s a = p a) → ‖s x‖ < ρ) →
  ∃ g : A, p g = 1 ∧ ‖R (x * (g * a₀ : A))‖ < ρ

def Asm : Prop := USide → G2s → MuEx → MatchUnit → MatchSplit → EndoBlock → StableBlock → RunC

end UpperTheory.V.Z.Tf.GlobalTraceComparison
