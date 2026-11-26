module

public import Formalism.ThetaLogCoordinates.FockResolutionOnto.ShiftLastLetterThresholds

@[expose] public section

section -- merged from Formalism.ThetaLogCoordinates.FockResolutionOnto.StatementC
namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM.M MvPolynomial Finset

def YCondDrop : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LL : Letters (K + 1)) (M : WithTop ℤ),
    LL.vec (Fin.last K) = true →
    ∀ F ∈ Pol p r LL, F ∈ YCond p LL (K + 1) M → F ∈ YCond p LL K M

def ResInto : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (e1 : ℕ),
    2 ≤ r → (ρ : ℕ) = r - 1 → LL.vec (Fin.last K) = true → HypP p LL ρ e1 →
    ∀ h ∈ Y p LL J M, initPart (Fin.last K, ρ) 0 h ∈ XSp p LL J M ρ

def ResMM : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) (e1 : ℕ),
    2 ≤ r → (ρ : ℕ) = r - 1 → LL.vec (Fin.last K) = true → HypP p LL ρ e1 → HypE p LL ρ e1 →
    ResOntoK p LL J M ρ →
    ∀ x, x ∈ XH p LL J M ρ w ↔ ∃ h ∈ MMw p LL J M ρ w, initPart (Fin.last K, ρ) 0 h = x

def ProjX : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) (e1 : ℕ),
    2 ≤ r → (ρ : ℕ) = r - 1 → LL.vec (Fin.last K) = true → HypP p LL ρ e1 → HypE p LL ρ e1 →
    ∃ Pr : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p],
      ∀ m : Fin (K + 1) × Fin r →₀ ℕ, MultiDeg LL m → m (Fin.last K, ρ) = 0 →
        Pr (monomial m 1) ∈ XH p LL J M ρ w ∧
        ((p : ℚ_[p]) ^ ((K + 3) * e1)) • Pr (monomial m 1) ∈ IntPol p (Fin (K + 1) × Fin r) ∧
        ∀ g ∈ XH p LL J M ρ w, fock p g (Pr (monomial m 1)) = fock p g (monomial m 1)

def ProjAtOf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) (e e1 : ℕ),
    2 ≤ r → (ρ : ℕ) = r - 1 → LLw.vec (Fin.last K) = true → e ≤ LLw.deg (Fin.last K) →
    HypP p (setLast LLw (LLw.deg (Fin.last K) - e)) ρ e1 → HypE p (setLast LLw (LLw.deg (Fin.last K) - e)) ρ e1 →
    ResOntoK p (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ →
    ProjAt p LLw J M ρ w e ((K + 3) * e1)

end Formalism.InvariantFactorPaths.L4
end

section -- merged from Formalism.ThetaLogCoordinates.FockResolutionOnto.StatementB
namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM.M MvPolynomial Finset

def FirstCoordinateRaisingCriterion : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (LL : Letters N) (j : ℕ) (M : WithTop ℤ)
    (F : MvPolynomial (Fin N × Fin r) ℚ_[p]),
    F ∈ YCond p LL j M ↔
      ∀ l : List (Fin r), ((l.map fun c => glAct p LL j 0 c).prod) F ∈
        MvPolynomial.restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ M}

def MulEarly : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LL : Letters (K + 1)) (j : ℕ) (M : WithTop ℤ) (c : Fin r)
    (h : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]), j ≤ K →
    (X (Fin.last K, c) * h ∈ YCond p LL j M ↔ h ∈ YCond p LL j M)

def MulLast : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LL : Letters (K + 1)) (j : ℕ) (M : WithTop ℤ) (c : Fin r)
    (h : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]), K + 1 ≤ j → LL.vec (Fin.last K) = true →
    (X (Fin.last K, c) * h ∈ YCond p LL j M ↔ h ∈ YCond p LL j (M + ((-1 : ℤ) : WithTop ℤ)))

def FilEq : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) (e : ℕ),
    LLw.vec (Fin.last K) = true → e ≤ LLw.deg (Fin.last K) →
    ∀ f, f ∈ FilE p LLw J M ρ w (Fin.last K, ρ) e ↔
      ∃ h ∈ MMwZ p (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ (shiftWt w ρ e),
        f = X (Fin.last K, ρ) ^ e * h

def FilBot : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) (e : ℕ),
    LLw.deg (Fin.last K) < e → FilE p LLw J M ρ w (Fin.last K, ρ) e = ⊥

def GrEq : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) (e : ℕ),
    LLw.vec (Fin.last K) = true → e ≤ LLw.deg (Fin.last K) →
    ∀ x, x ∈ grLat p LLw J M ρ w (Fin.last K, ρ) e ↔
      ∃ h ∈ MMwZ p (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ (shiftWt w ρ e),
        x = X (Fin.last K, ρ) ^ e * initPart (Fin.last K, ρ) 0 h

def GrBot : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) (e : ℕ),
    LLw.deg (Fin.last K) < e → grLat p LLw J M ρ w (Fin.last K, ρ) e = ⊥

end Formalism.InvariantFactorPaths.L4
end
