module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedTransport
public import Formalism.PieriBlockIdeals.PieriColumnMinors.RowGenDerivative
public import GroundTheory.Brauer.Degree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypesJointShapeBlockUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStrictHenselisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryGroupFamilyZariskiDense
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumNormRowSubProdMinors

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockOperatorsLieRepresentationCommute
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockOperatorsLieRepresentationCommute
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.FockAlg


open MvPolynomial in
theorem _root_.GlobalTheory.FockAlg.fock_lie_and_commute : ∀ (p q r s : ℕ),
    (∀ Y Z, _root_.Formalism.BasicNotions.TH.omAct p q r s (Y * Z - Z * Y) =
      _root_.Formalism.BasicNotions.TH.omAct p q r s Y * _root_.Formalism.BasicNotions.TH.omAct p q r s Z - _root_.Formalism.BasicNotions.TH.omAct p q r s Z * _root_.Formalism.BasicNotions.TH.omAct p q r s Y) ∧
    _root_.Formalism.BasicNotions.TH.IsLieAct (_root_.Formalism.BasicNotions.TH.fockAct1 p q r s) ∧ _root_.Formalism.BasicNotions.TH.IsLieAct (_root_.Formalism.BasicNotions.TH.fockAct2 p q r s) ∧
    ∀ Y Z, _root_.Formalism.BasicNotions.TH.fockAct1 p q r s Y * _root_.Formalism.BasicNotions.TH.fockAct2 p q r s Z = _root_.Formalism.BasicNotions.TH.fockAct2 p q r s Z * _root_.Formalism.BasicNotions.TH.fockAct1 p q r s Y :=
  fun p q r s => ⟨_root_.GlobalTheory.FockLie.omAct_lie p q r s,
    _root_.GlobalTheory.FockPair.pair_lie_commute p q r s⟩

end GlobalTheory.FockAlg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockOperatorsLieRepresentationCommuteStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockOperators_lie_representation_commute : ∀ (p q r s : ℕ), (∀ Y Z, omAct p q r s (Y * Z - Z * Y) = omAct p q r s Y * omAct p q r s Z - omAct p q r s Z * omAct p q r s Y) ∧ IsLieAct (fockAct1 p q r s) ∧ IsLieAct (fockAct2 p q r s) ∧ ∀ Y Z, fockAct1 p q r s Y * fockAct2 p q r s Z = fockAct2 p q r s Z * fockAct1 p q r s Y := by
  first | exact @GlobalTheory.FockAlg.fock_lie_and_commute | exact GlobalTheory.FockAlg.fock_lie_and_commute | (intros; apply GlobalTheory.FockAlg.fock_lie_and_commute <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaSchur
open MvPolynomial Formalism.GradedWeylDivisibility TensorProduct

noncomputable section

namespace GlobalTheory.LeviCut

def GlRel (N : ℕ) {A : Type} [Ring A] (e : ℕ → ℕ → A) : Prop :=
  ∀ a b c d : ℕ, a < N → b < N → c < N → d < N →
    e a b * e c d - e c d * e a b = (if b = c then e a d else 0) - (if d = a then e c b else 0)

def coef (j k : ℕ) : ℚ := (-1) ^ k * (j.factorial : ℚ) / ((k.factorial : ℚ) * ((k + j + 1).factorial : ℚ))

def proj {A : Type} [Ring A] [Algebra ℚ A] (K j : ℕ) (X Y : A) : A :=
  ∑ k ∈ Finset.range (K + 1), coef j k • (Y ^ k * X ^ k)

def rootP {A : Type} [Ring A] [Algebra ℚ A] (D : ℕ → ℕ → A) (K i j : ℕ) : A :=
  proj K (j - i - 1) (D i j) (D j i)

def rowP {A : Type} [Ring A] [Algebra ℚ A] (D : ℕ → ℕ → A) (K i s n : ℕ) : A :=
  ((List.range' s n).map (rootP D K i)).prod

def gridP {A : Type} [Ring A] [Algebra ℚ A] (D : ℕ → ℕ → A) (K a b t : ℕ) : A :=
  ((List.range t).reverse.map fun i => rowP D K i a b).prod

def adj {A : Type} [Ring A] [Algebra ℚ A] (x : A) : Module.End ℚ A :=
  LinearMap.mulLeft ℚ x - LinearMap.mulRight ℚ x

def IsWt (N : ℕ) {V : Type} [AddCommGroup V] [Module ℚ V] (e : ℕ → ℕ → Module.End ℚ V) (μ : ℕ → ℤ) (x : V) : Prop :=
  ∀ c < N, e c c x = (μ c : ℚ) • x

def Bdd (N K : ℕ) {V : Type} [AddCommGroup V] [Module ℚ V] (e : ℕ → ℕ → Module.End ℚ V) : Prop :=
  ∀ a < N, ∀ b < N, ∀ (n : ℤ) (x : V), e a a x - e b b x = (n : ℚ) • x → (K : ℤ) < n → x = 0

def Dom (N : ℕ) {V : Type} [AddCommGroup V] [Module ℚ V] (e : ℕ → ℕ → Module.End ℚ V) (lam : ℕ → ℤ) : Prop :=
  ∀ (μ : ℕ → ℤ) (x : V), IsWt N e μ x → x ≠ 0 →
    (∀ k ≤ N, ∑ c ∈ Finset.range k, μ c ≤ ∑ c ∈ Finset.range k, lam c) ∧
      ∑ c ∈ Finset.range N, μ c = ∑ c ∈ Finset.range N, lam c

def WtSpan (N : ℕ) {V : Type} [AddCommGroup V] [Module ℚ V] (e : ℕ → ℕ → Module.End ℚ V) : Prop :=
  Submodule.span ℚ {x : V | ∃ μ : ℕ → ℤ, IsWt N e μ x} = ⊤

def DivStable (N : ℕ) {V : Type} [AddCommGroup V] [Module ℚ V] (e : ℕ → ℕ → Module.End ℚ V)
    (L : Submodule ℤ V) : Prop :=
  ∀ i < N, ∀ j < N, i ≠ j → ∀ k : ℕ, ∀ x ∈ L, ((k.factorial : ℚ)⁻¹) • (e i j ^ k) x ∈ L

def RankOne : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module ℚ W] (N K : ℕ) (D : ℕ → ℕ → Module.End ℚ W), GlRel N D → Bdd N (2 * K) D →
    ∀ o q : ℕ, o < N → q < N → o ≠ q → ∀ T : W, D o o T = 0 → D q q T = 0 →
      D o q (proj K 0 (D o q) (D q o) T) = 0 ∧ (D o q T = 0 → D q o T = 0)

def RankTwo : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module ℚ W] (N K : ℕ) (D : ℕ → ℕ → Module.End ℚ W), GlRel N D → Bdd N (2 * K) D →
    ∀ o p q : ℕ, o < N → p < N → q < N → o ≠ p → o ≠ q → p ≠ q → ∀ (j : ℕ) (T : W),
      D o o T = 0 → D p p T = 0 → D q q T = 0 → D p q T = 0 →
      D p q (proj K j (D o p) (D p o) (proj K (j + 1) (D o q) (D q o) T)) = 0

def GridInv : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module ℚ W] (a b K : ℕ) (D : ℕ → ℕ → Module.End ℚ W), GlRel (a + b) D →
    Bdd (a + b) (2 * K) D → ∀ T : W, (∀ c < a + b, ∀ d < a + b, (c < a ↔ d < a) → D c d T = 0) →
      ∀ c < a + b, ∀ d < a + b, D c d (gridP D K a b a T) = 0

def AdjBdd : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℚ V] (N K : ℕ) (e : ℕ → ℕ → Module.End ℚ V), GlRel N e → Bdd N K e →
    WtSpan N e → GlRel N (fun a b => adj (e a b)) ∧ Bdd N (2 * K) (fun a b => adj (e a b))

def StepScalar : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℚ V] (E F H T : Module.End ℚ V) (v : V) (φ : V →ₗ[ℚ] ℚ) (n K j : ℕ),
    E * F - F * E = H → H * F - F * H = -(F + F) → E v = 0 → H v = (n : ℚ) • v → n ≤ K → (∀ x, φ (F x) = 0) →
    (∀ k : ℕ, 0 < k → T ((F ^ k) v) = 0) →
      φ (proj K j (adj E) (adj F) T v) * ((n : ℚ) + j + 1) = φ (T v)

def GridScalar : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℚ V] (a b K : ℕ) (e : ℕ → ℕ → Module.End ℚ V) (lam : ℕ → ℤ) (v : V)
    (φ : V →ₗ[ℚ] ℚ) (T : Module.End ℚ V), GlRel (a + b) e → Dom (a + b) e lam → IsWt (a + b) e lam v →
    (∀ i j : ℕ, i < j → j < a + b → e i j v = 0 ∧ (∀ x, φ (e j i x) = 0) ∧ lam j ≤ lam i ∧ lam i ≤ lam j + K) →
    (∀ (μ : ℕ → ℤ) (x : V), IsWt (a + b) e μ x → ∑ c ∈ Finset.range a, μ c < ∑ c ∈ Finset.range a, lam c → T x = 0) →
      φ (gridP (fun c d => adj (e c d)) K a b a T v) *
        ((∏ i ∈ Finset.range a, ∏ j ∈ Finset.Ico a (a + b), (lam i - lam j + (j : ℤ) - (i : ℤ)) : ℤ) : ℚ) = φ (T v)

def GridInt : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℚ V] (a b K w Λ : ℕ) (e : ℕ → ℕ → Module.End ℚ V) (L M : Submodule ℤ V),
    DivStable (a + b) e L → DivStable (a + b) e M → K + (a + b) ≤ w + 1 →
    (∀ j k : ℕ, j + k + 1 ≤ w → (j + k + 1).factorial ∣ Λ * (j.factorial * k.factorial)) →
    ∀ (c : ℕ) (T : Module.End ℚ V), (∀ x ∈ L, (c : ℤ) • T x ∈ M) →
      ∀ x ∈ L, ((c * Λ ^ (a * b) : ℕ) : ℤ) • gridP (fun c d => adj (e c d)) K a b a T x ∈ M

def BetaDen : Prop :=
  ∀ l w : ℕ, l.Prime → ∃ m : ℕ, ¬ l ∣ m ∧
    ∀ j k : ℕ, j + k + 1 ≤ w → (j + k + 1).factorial ∣ (m * l ^ Nat.log l w) * (j.factorial * k.factorial)

def eV (N : ℕ) (ν : Fin N → ℕ) (a b : ℕ) : Module.End ℚ (dualWeyl ℚ N N ν) :=
  if h : a < N ∧ b < N then
    LinearMap.restrict (Formalism.CohomologicalDescent.LR.der N N ⟨a, h.1⟩ ⟨b, h.2⟩ : Module.End ℚ (MvPolynomial (Fin N × Fin N) ℚ))
      (fun f hf => Formalism.CohomologicalDescent.LR.der_mem ν _ _ f hf)
  else 0

def latV (N : ℕ) (ν : Fin N → ℕ) (M : Submodule ℤ (MvPolynomial (Fin N × Fin N) ℤ)) : Submodule ℤ (dualWeyl ℚ N N ν) :=
  (M.map (intQ N N)).comap ((dualWeyl ℚ N N ν).subtype.restrictScalars ℤ)

def wtZ {N : ℕ} (ν : Fin N → ℕ) (c : ℕ) : ℤ := if h : c < N then (ν ⟨c, h⟩ : ℤ) else 0

def resVarT (R : Type) [CommRing R] (p q : ℕ) (v : Fin (p + q) × Fin (p + q)) :
    MvPolynomial (Fin p × Fin p) R ⊗[R] MvPolynomial (Fin q × Fin q) R :=
  Fin.addCases (motive := fun _ => MvPolynomial (Fin p × Fin p) R ⊗[R] MvPolynomial (Fin q × Fin q) R)
    (fun a => Fin.addCases (motive := fun _ => MvPolynomial (Fin p × Fin p) R ⊗[R] MvPolynomial (Fin q × Fin q) R)
      (fun s => X (a, s) ⊗ₜ[R] 1) (fun _ => 0) v.2)
    (fun b => Fin.addCases (motive := fun _ => MvPolynomial (Fin p × Fin p) R ⊗[R] MvPolynomial (Fin q × Fin q) R)
      (fun _ => 0) (fun t => 1 ⊗ₜ[R] X (b, t)) v.2) v.1

def resT (R : Type) [CommRing R] (p q : ℕ) : MvPolynomial (Fin (p + q) × Fin (p + q)) R →ₐ[R]
    MvPolynomial (Fin p × Fin p) R ⊗[R] MvPolynomial (Fin q × Fin q) R :=
  aeval (resVarT R p q)

def NablaGl : Prop :=
  ∀ (N : ℕ) (ν : Fin N → ℕ), Antitone ν →
    GlRel N (eV N ν) ∧ WtSpan N (eV N ν) ∧ Dom N (eV N ν) (wtZ ν) ∧
      DivStable N (eV N ν) (latV N ν (dualWeyl ℤ N N ν)) ∧ DivStable N (eV N ν) (latV N ν (weyl ℤ N N le_rfl ν))

def NablaBdd : Prop :=
  ∀ (N : ℕ) (ν : Fin N → ℕ), Antitone ν → ∀ K : ℕ, (∀ i j, ν i ≤ ν j + K) → Bdd N K (eV N ν)

def NablaSchur : Prop :=
  ∀ (N : ℕ) (ν : Fin N → ℕ) (hν : Antitone ν) (S : Module.End ℚ (dualWeyl ℚ N N ν)),
    (∀ c < N, ∀ d < N, eV N ν c d * S = S * eV N ν c d) →
    fockQ (hw ℚ le_rfl ν) (S ⟨hw ℚ le_rfl ν, hwMem ℚ N N le_rfl ν hν⟩ : dualWeyl ℚ N N ν) =
      fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) → S = 1

def SubstMem : Prop :=
  ∀ (R : Type) [CommRing R] (k N : ℕ) (τ : Fin k → Fin N), StrictMono τ →
    ∀ ψ : Fin N × Fin N → MvPolynomial (Fin k × Fin k) R,
      (∀ a s, ψ (τ a, τ s) = X (a, s)) → (∀ x s, x ∉ Set.range τ → ψ (x, τ s) = 0) →
      (∀ x y, y ∉ Set.range τ → ∃ c : R, ψ (x, y) = C c) →
      ∀ (ν : Fin N → ℕ), ∀ f ∈ dualWeyl R N N ν, aeval ψ f ∈ dualWeyl R k k (fun s => ν (τ s))

def ResLat : Prop :=
  ∀ (p q : ℕ) (ν : Fin (p + q) → ℕ), ∀ f ∈ dualWeyl ℤ (p + q) (p + q) ν,
    resT ℚ p q (intQ (p + q) (p + q) f) ∈ Submodule.span ℤ
      {z | ∃ f₁ ∈ dualWeyl ℤ p p (fun i => ν (Fin.castAdd q i)), ∃ f₂ ∈ dualWeyl ℤ q q (fun j => ν (Fin.natAdd p j)),
        z = intQ p p f₁ ⊗ₜ[ℚ] intQ q q f₂}

def ResHw : Prop :=
  ∀ (p q : ℕ) (ν : Fin (p + q) → ℕ), Antitone ν →
    resT ℚ p q (hw ℚ le_rfl ν) =
      hw ℚ le_rfl (fun i => ν (Fin.castAdd q i)) ⊗ₜ[ℚ] hw ℚ le_rfl (fun j => ν (Fin.natAdd p j))

def ResDer : Prop :=
  ∀ (p q : ℕ) (f : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ),
    (∀ c d : Fin p, resT ℚ p q (Formalism.CohomologicalDescent.LR.der (p + q) (p + q) (Fin.castAdd q c) (Fin.castAdd q d) f) =
      LinearMap.rTensor _ (Formalism.CohomologicalDescent.LR.der p p c d : Module.End ℚ (MvPolynomial (Fin p × Fin p) ℚ)) (resT ℚ p q f)) ∧
    (∀ c d : Fin q, resT ℚ p q (Formalism.CohomologicalDescent.LR.der (p + q) (p + q) (Fin.natAdd p c) (Fin.natAdd p d) f) =
      LinearMap.lTensor _ (Formalism.CohomologicalDescent.LR.der q q c d : Module.End ℚ (MvPolynomial (Fin q × Fin q) ℚ)) (resT ℚ p q f)) ∧
    ∀ (ν : Fin (p + q) → ℕ) (t : ℚ), IsWeightedHomogeneous (colW (p + q) (p + q)) f ν →
      ∑ c : Fin p, Formalism.CohomologicalDescent.LR.der (p + q) (p + q) (Fin.castAdd q c) (Fin.castAdd q c) f = t • f →
      t ≠ ∑ c : Fin p, (ν (Fin.castAdd q c) : ℚ) → resT ℚ p q f = 0

def LeviProj : Prop :=
  ∀ (p q : ℕ) (ν : Fin (p + q) → ℕ) (hν : Antitone ν) (c₁ c₂ : ℕ),
    (∀ x ∈ dualWeyl ℤ p p (fun i => ν (Fin.castAdd q i)), (c₁ : ℤ) • x ∈ weyl ℤ p p le_rfl (fun i => ν (Fin.castAdd q i))) →
    (∀ x ∈ dualWeyl ℤ q q (fun j => ν (Fin.natAdd p j)), (c₂ : ℤ) • x ∈ weyl ℤ q q le_rfl (fun j => ν (Fin.natAdd p j))) →
    ∃ T : Module.End ℚ (dualWeyl ℚ (p + q) (p + q) ν),
      (∀ c < p + q, ∀ d < p + q, (c < p ↔ d < p) → eV (p + q) ν c d * T = T * eV (p + q) ν c d) ∧
      (∀ x ∈ latV (p + q) ν (dualWeyl ℤ (p + q) (p + q) ν),
        ((c₁ * c₂ : ℕ) : ℤ) • T x ∈ latV (p + q) ν (weyl ℤ (p + q) (p + q) le_rfl ν)) ∧
      (∀ (μ : ℕ → ℤ) (x : dualWeyl ℚ (p + q) (p + q) ν), IsWt (p + q) (eV (p + q) ν) μ x →
        ∑ c ∈ Finset.range p, μ c < ∑ c ∈ Finset.range p, wtZ ν c → T x = 0) ∧
      fockQ (hw ℚ le_rfl ν) (T ⟨hw ℚ le_rfl ν, hwMem ℚ (p + q) (p + q) le_rfl ν hν⟩ : dualWeyl ℚ (p + q) (p + q) ν) =
        fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν)

end GlobalTheory.LeviCut
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeMinpolyLeBaseChange
open Module Polynomial TensorProduct

namespace GlobalTheory.CentSep

theorem aeval_mem_span_pow {K S : Type} [Field K] [Ring S] [Nontrivial S] [Algebra K S] (x : S)
    (hx : IsIntegral K x) (q : K[X]) :
    aeval x q ∈ Submodule.span K (Set.range fun j : Fin (minpoly K x).natDegree => x ^ (j : ℕ)) := by
  have hm := minpoly.monic hx
  rw [← aeval_modByMonic_eq_self_of_root (p := q) (minpoly.aeval K x)]
  have hne : minpoly K x ≠ 1 := by
    intro h
    have := minpoly.natDegree_pos hx
    rw [h, natDegree_one] at this
    exact lt_irrefl _ this
  have hlt := natDegree_modByMonic_lt q hm hne
  rw [aeval_eq_sum_range' hlt]
  exact Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨⟨j, Finset.mem_range.mp hj⟩, rfl⟩)

theorem centralizer_toSubmodule {K S : Type} [Field K] [Ring S] [Algebra K S] (g : S) :
    Subalgebra.toSubmodule (Subalgebra.centralizer K ({g} : Set S)) =
      LinearMap.ker (LinearMap.mulLeft K g - LinearMap.mulRight K g) := by
  ext y
  simp [Subalgebra.mem_centralizer_iff, sub_eq_zero]

theorem natDegree_minpoly_le_baseChange {F A : Type} [Field F] [Ring A] [Algebra F A] (K : Type)
    [Field K] [Algebra F K] (g : A) (hK : IsIntegral K ((1 : K) ⊗ₜ[F] g)) :
    (minpoly F g).natDegree ≤ (minpoly K ((1 : K) ⊗ₜ[F] g)).natDegree := by
  set x : K ⊗[F] A := (1 : K) ⊗ₜ[F] g with hx
  have hli : LinearIndependent K (fun j : Fin (minpoly F g).natDegree => x ^ (j : ℕ)) := by
    have h := Module.Flat.linearIndependent_one_tmul (S := K) (linearIndependent_pow (K := F) g)
    convert h using 1
    funext j
    simp [hx, Algebra.TensorProduct.tmul_pow]
  by_contra hlt
  push_neg at hlt
  have hsum := aeval_eq_sum_range' hlt x
  rw [minpoly.aeval, ← Fin.sum_univ_eq_sum_range (fun i => (minpoly K x).coeff i • x ^ i)] at hsum
  have hc := Fintype.linearIndependent_iff.mp hli (fun i => (minpoly K x).coeff i) hsum.symm
  apply minpoly.ne_zero hK
  ext i
  rw [coeff_zero]
  by_cases hi : i < (minpoly F g).natDegree
  · exact hc ⟨i, hi⟩
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

theorem centralizer_eq_adjoin : ∀ (F B : Type) [Field F] [Ring B] [Algebra F B]
    [Algebra.IsCentral F B] [IsSimpleRing B] [FiniteDimensional F B] (n : ℕ),
    Module.finrank F B = n ^ 2 → ∀ g : B, (minpoly F g).Separable →
      (minpoly F g).natDegree = n → Subalgebra.centralizer F {g} = Algebra.adjoin F {g} := by
  intro F B _ _ _ _ _ _ n hB g hsep hdeg
  classical
  obtain ⟨k, hk0, hkB, ⟨e⟩⟩ := GroundTheory.Brauer.exists_algEquiv_matrix_algebraicClosure F B
  have hkn : k = n := Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) (hkB.symm.trans hB)
  subst hkn
  set K := AlgebraicClosure F
  set x : K ⊗[F] B := (1 : K) ⊗ₜ[F] g with hx
  have hxi : IsIntegral K x := IsIntegral.of_finite K x

  have hxr : x = Algebra.TensorProduct.includeRight g := rfl
  have hdvd : minpoly K x ∣ (minpoly F g).map (algebraMap F K) := by
    apply minpoly.dvd
    rw [aeval_map_algebraMap, hxr, aeval_algHom_apply, minpoly.aeval, map_zero]
  have hge := natDegree_minpoly_le_baseChange K g hxi
  rw [hdeg] at hge
  have hle : (minpoly K x).natDegree ≤ k := by
    have hmap : (minpoly F g).map (algebraMap F K) ≠ 0 :=
      (Polynomial.map_ne_zero_iff (algebraMap F K).injective).mpr (minpoly.ne_zero (IsIntegral.of_finite F g))
    calc (minpoly K x).natDegree ≤ ((minpoly F g).map (algebraMap F K)).natDegree :=
          natDegree_le_of_dvd hdvd hmap
      _ = k := by rw [natDegree_map, hdeg]
  have hxdeg : (minpoly K x).natDegree = k := le_antisymm hle hge

  set N := e x with hN
  have hmN : minpoly K N = minpoly K x := minpoly.algEquiv_eq e x
  have hchar : N.charpoly = minpoly K x := by
    have hd : minpoly K N ∣ N.charpoly := minpoly.dvd K N (Matrix.aeval_self_charpoly N)
    rw [hmN] at hd
    have := eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le (minpoly.monic hxi) hd
      (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, hxdeg])
    rw [this, (Matrix.charpoly_monic N).leadingCoeff, C_1, one_mul]
  have hNsep : N.charpoly.Separable := by
    rw [hchar]
    exact (hsep.map).of_dvd hdvd

  have hCK : Subalgebra.toSubmodule (Subalgebra.centralizer K ({x} : Set (K ⊗[F] B))) ≤
      Submodule.span K (Set.range fun j : Fin (minpoly K x).natDegree => x ^ (j : ℕ)) := by
    intro y hy
    have hy' : x * y = y * x :=
      (Subalgebra.mem_centralizer_iff K).mp hy x (Set.mem_singleton x)
    have hcomm : Commute (e y) N := by
      change e y * e x = e x * e y
      rw [← map_mul, ← map_mul, hy']
    obtain ⟨q, hq⟩ := GlobalTheory.T.matrix_eq_aeval_of_commute_of_charpoly_separable k N (e y) hNsep hcomm
    have : y = aeval x q := by
      apply e.injective
      rw [hq, hN, ← aeval_algHom_apply]
    rw [this]
    exact aeval_mem_span_pow x hxi q
  have hfinK : finrank K (Subalgebra.toSubmodule (Subalgebra.centralizer K ({x} : Set (K ⊗[F] B))))
      ≤ k := by
    calc _ ≤ finrank K (Submodule.span K
            (Set.range fun j : Fin (minpoly K x).natDegree => x ^ (j : ℕ))) :=
          Submodule.finrank_mono hCK
      _ ≤ Fintype.card (Fin (minpoly K x).natDegree) := finrank_range_le_card _
      _ = k := by rw [Fintype.card_fin, hxdeg]

  have hbc := (GlobalTheory.BadCount.finrank_iInf_ker_baseChange F K B (K ⊗[F] B) Unit
    (TensorProduct.mk F K B 1) (TensorProduct.isBaseChange F B K)
    (fun _ => LinearMap.mulLeft F g - LinearMap.mulRight F g)
    (fun _ => LinearMap.mulLeft K x - LinearMap.mulRight K x)
    (fun _ v => by
      simp [hx, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.tmul_sub])).1
  rw [_root_.iInf_const, _root_.iInf_const] at hbc
  rw [← centralizer_toSubmodule, ← centralizer_toSubmodule] at hbc

  have hadj : Algebra.adjoin F ({g} : Set B) ≤ Subalgebra.centralizer F {g} :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr
      ((Subalgebra.mem_centralizer_iff F).mpr fun h hh => by rw [Set.mem_singleton_iff.mp hh]))
  have hspan : Submodule.span F (Set.range fun j : Fin (minpoly F g).natDegree => g ^ (j : ℕ)) ≤
      Subalgebra.toSubmodule (Algebra.adjoin F ({g} : Set B)) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact pow_mem (Algebra.subset_adjoin (Set.mem_singleton g)) _
  have hfinS : k ≤ finrank F (Subalgebra.toSubmodule (Algebra.adjoin F ({g} : Set B))) := by
    calc k = Fintype.card (Fin (minpoly F g).natDegree) := by rw [Fintype.card_fin, hdeg]
      _ = finrank F (Submodule.span F
            (Set.range fun j : Fin (minpoly F g).natDegree => g ^ (j : ℕ))) :=
          (finrank_span_eq_card (linearIndependent_pow g)).symm
      _ ≤ _ := Submodule.finrank_mono hspan
  have heq := Submodule.eq_of_le_of_finrank_le
    (Subalgebra.toSubmodule.monotone hadj) (by rw [← hbc]; exact hfinK.trans hfinS)
  exact (Subalgebra.toSubmodule_injective heq).symm

end GlobalTheory.CentSep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypesJointShapeBlockInUnitaryS
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypesJointShapeBlockInUnitaryS
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.TypesMirror

theorem sameBlock_swap {p q : ℕ} (a b : Ix p q) :
    sameBlock (p := q) (q := p) a.swap b.swap ↔ sameBlock a b := by
  cases a <;> cases b <;> simp [sameBlock]

theorem card_filter_swap {p q : ℕ} (P : Ix p q → Prop) (Q : Ix q p → Prop)
    [DecidablePred P] [DecidablePred Q] (h : ∀ b, P b ↔ Q b.swap) :
    (Finset.univ.filter P).card = (Finset.univ.filter Q).card := by
  refine Finset.card_equiv (Equiv.sumComm (Fin p) (Fin q)) ?_
  intro b
  simpa using h b

theorem blattner_swap {p q : ℕ} (lam : Ix q p → ℚ) (a : Ix p q) :
    blattner (fun b : Ix p q => lam b.swap) a = blattner lam a.swap := by
  unfold blattner rhoNC
  rw [card_filter_swap (fun b : Ix p q => ¬ sameBlock a b ∧ lam b.swap < lam a.swap)
      (fun b : Ix q p => ¬ sameBlock a.swap b ∧ lam b < lam a.swap)
      (fun b => by rw [sameBlock_swap]),
    card_filter_swap (fun b : Ix p q => ¬ sameBlock a b ∧ lam a.swap < lam b.swap)
      (fun b : Ix q p => ¬ sameBlock a.swap b ∧ lam a.swap < lam b)
      (fun b => by rw [sameBlock_swap]),
    card_filter_swap (fun b : Ix p q => sameBlock a b ∧ lam b.swap < lam a.swap)
      (fun b : Ix q p => sameBlock a.swap b ∧ lam b < lam a.swap)
      (fun b => by rw [sameBlock_swap]),
    card_filter_swap (fun b : Ix p q => sameBlock a b ∧ lam a.swap < lam b.swap)
      (fun b : Ix q p => sameBlock a.swap b ∧ lam a.swap < lam b)
      (fun b => by rw [sameBlock_swap])]

theorem shiftNu_swap {p q : ℕ} (r s : ℕ) (lam : Ix q p → ℚ) (a : Ix p q) :
    shiftNu (cPair r s) (blattner (fun b : Ix p q => lam b.swap)) a =
      shiftNu (cPair s r) (blattner lam) a.swap := by
  cases a <;> simp only [shiftNu, blattner_swap, Sum.swap_inl, Sum.swap_inr, cPair] <;> ring

theorem ofBlocks_swap {p q : ℕ} (l₁ l₂ : List ℚ) :
    (ofBlocks l₁ l₂ : Ix p q → ℚ) = fun b => (ofBlocks l₂ l₁ : Ix q p → ℚ) b.swap := by
  funext b; cases b <;> rfl

theorem isParam_swap {p q : ℕ} (lam : Ix q p → ℚ) (h : IsParam lam) :
    IsParam (fun b : Ix p q => lam b.swap) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1.comp (Equiv.sumComm (Fin p) (Fin q)).injective, ?_, fun a => h3 _, fun a b => h4 _ _⟩
  intro a b hab
  apply h2
  cases a <;> cases b <;> simpa [posC] using hab

theorem jointShape_swap {p q r s : ℕ} (lam : Ix q p → ℚ) (lam' : Ix s r → ℚ)
    (h : JointShape q p s r (blattner lam) (blattner lam')) :
    JointShape p q r s (blattner fun b => lam b.swap) (blattner fun b => lam' b.swap) := by
  obtain ⟨a, b, c, d, ha, hc, hb, hd, pa, pb, pc, pd, l1, l2, l3, l4, e1, e2⟩ := h
  refine ⟨c, d, a, b, hc, ha, hd, hb, pc, pd, pa, pb, l2, l1, l4, l3, ?_, ?_⟩
  · funext x
    rw [shiftNu_swap, e1, ofBlocks_swap]
    simp
  · funext x
    rw [shiftNu_swap, e2, ofBlocks_swap]
    simp

theorem hypA_swap {t : ℕ} {al be ga de : List ℚ} (h : HypA t al be ga de) :
    HypA t ga de al be := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  have hp : (ga ++ de ++ al ++ be).Perm (al ++ be ++ ga ++ de) := by
    rw [List.append_assoc (ga ++ de), List.append_assoc (al ++ be)]
    exact List.perm_append_comm
  refine ⟨h1, by omega, h5, h6, h3, h4, hp.nodup_iff.mpr h7,
    fun e he => h8 e (List.perm_append_comm.mem_iff.mp he),
    fun e he => h9 e (List.perm_append_comm.mem_iff.mp he),
    fun e he => h10 e (hp.mem_iff.mp he), fun e he => h11 e (hp.mem_iff.mp he)⟩

theorem types_mirror : ∀ (t : ℕ) (al be ga de : List ℚ), HypA t al be ga de → JointShape _ _ _ _ (blattner (lamA al be ga de)) (blattner (lamM' t al be ga de)) ∧ IsParam (lamM' t al be ga de) ∧ (∀ a, (0 < lamA al be ga de a → 0 ≤ shiftNu (cPair (al.length + de.length) (ga.length + be.length + t)) (blattner (lamA al be ga de)) a) ∧ (lamA al be ga de a < 0 → shiftNu (cPair (al.length + de.length) (ga.length + be.length + t)) (blattner (lamA al be ga de)) a ≤ 0)) ∧ (∀ c, ((t : ℚ) / 2 < lamM' t al be ga de c → 0 ≤ shiftNu (cPair (al.length + be.length) (ga.length + de.length)) (blattner (lamM' t al be ga de)) c) ∧ (lamM' t al be ga de c ≤ (t : ℚ) / 2 → shiftNu (cPair (al.length + be.length) (ga.length + de.length)) (blattner (lamM' t al be ga de)) c ≤ 0)) := by
  intro t al be ga de h
  obtain ⟨k1, -, k3, k4, k5⟩ := GlobalTheory.T.lowest_kTypes_jointShape_block_unitary t ga de al be (hypA_swap h)
  have e1 : lamA al be ga de = fun b => lamA ga de al be b.swap := ofBlocks_swap _ _
  have e2 : lamM' t al be ga de = fun b => lamA' t ga de al be b.swap := ofBlocks_swap _ _
  rw [e1, e2]
  refine ⟨jointShape_swap _ _ k1, isParam_swap _ k3, fun a => ?_, fun c => ?_⟩
  · rw [shiftNu_swap]; exact k4 a.swap
  · rw [shiftNu_swap]; exact k5 c.swap

end GlobalTheory.TypesMirror
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypesJointShapeBlockInUnitarySStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowestKTypes_jointShape_block_in_unitaryS : ∀ (t : ℕ) (al be ga de : List ℚ), HypA t al be ga de → JointShape _ _ _ _ (blattner (lamA al be ga de)) (blattner (lamM' t al be ga de)) ∧ IsParam (lamM' t al be ga de) ∧ (∀ a, (0 < lamA al be ga de a → 0 ≤ shiftNu (cPair (al.length + de.length) (ga.length + be.length + t)) (blattner (lamA al be ga de)) a) ∧ (lamA al be ga de a < 0 → shiftNu (cPair (al.length + de.length) (ga.length + be.length + t)) (blattner (lamA al be ga de)) a ≤ 0)) ∧ (∀ c, ((t : ℚ) / 2 < lamM' t al be ga de c → 0 ≤ shiftNu (cPair (al.length + be.length) (ga.length + de.length)) (blattner (lamM' t al be ga de)) c) ∧ (lamM' t al be ga de c ≤ (t : ℚ) / 2 → shiftNu (cPair (al.length + be.length) (ga.length + de.length)) (blattner (lamM' t al be ga de)) c ≤ 0)) := by
  first | exact @GlobalTheory.TypesMirror.types_mirror | exact GlobalTheory.TypesMirror.types_mirror | (intros; apply GlobalTheory.TypesMirror.types_mirror <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankIInfKerSemilinearStandardBasis
open Module

namespace GlobalTheory.BadCount

theorem finrank_iInf_ker_semilinear : ∀ (K V ι : Type) [Field K] [AddCommGroup V] [Module ℂ V]
    [Finite ι] (σ : K →+* ℂ) (N : ℕ) (f : (Fin N → K) →ₛₗ[σ] V),
    (LinearIndependent ℂ fun k => f (Pi.single k 1)) → Submodule.span ℂ (Set.range f) = ⊤ →
    ∀ (a : ι → (Fin N → K) →ₗ[K] (Fin N → K)) (a' : ι → V →ₗ[ℂ] V),
      (∀ i v, a' i (f v) = f (a i v)) →
      finrank ℂ (⨅ i, LinearMap.ker (a' i) : Submodule ℂ V) =
        finrank K (⨅ i, LinearMap.ker (a i) : Submodule K (Fin N → K)) := by
  intro K V ι _ _ _ _ σ N f hli hsp a a' ha
  letI : Algebra K ℂ := σ.toAlgebra
  letI : Module K V := Module.compHom V σ
  haveI : IsScalarTower K ℂ V := ⟨fun k c v => by
    show (σ k * c) • v = σ k • c • v
    rw [mul_smul]⟩
  let g : (Fin N → K) →ₗ[K] V :=
    { toFun := f, map_add' := f.map_add, map_smul' := fun k x => f.map_smulₛₗ k x }
  have hsp' : Submodule.span ℂ (Set.range fun k => f (Pi.single k 1)) = ⊤ := by
    rw [eq_top_iff, ← hsp, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← (Pi.basisFun K (Fin N)).sum_repr x, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [f.map_smulₛₗ, Pi.basisFun_apply]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  let c : Basis (Fin N) ℂ V := Basis.mk hli hsp'.ge
  have hc : ∀ k, c k = f (Pi.single k 1) := fun k => Basis.mk_apply _ _ _
  let e := (Algebra.TensorProduct.basis ℂ (Pi.basisFun K (Fin N))).equiv c (Equiv.refl _)
  have hbc : IsBaseChange ℂ g := by
    refine IsBaseChange.of_equiv e fun m => ?_
    have h : (e.toLinearMap.restrictScalars K ∘ₗ TensorProduct.mk K ℂ (Fin N → K) 1) = g := by
      refine (Pi.basisFun K (Fin N)).ext fun k => ?_
      have := (Algebra.TensorProduct.basis ℂ (Pi.basisFun K (Fin N))).equiv_apply k c (Equiv.refl _)
      rw [Algebra.TensorProduct.basis_apply] at this
      simp only [LinearMap.coe_comp, Function.comp_apply, TensorProduct.mk_apply,
        LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
      rw [this, Equiv.refl_apply, hc, Pi.basisFun_apply]
      rfl
    exact congrArg (fun φ => φ m) h
  exact (finrank_iInf_ker_baseChange K ℂ (Fin N → K) V ι g hbc a a' ha).1

end GlobalTheory.BadCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictHenselisationEtaleOverPolynomial
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictHenselisationEtaleOverPolynomial
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory

open IsLocalRing Polynomial in
open scoped TensorProduct in
theorem _root_.GlobalTheory.comap_maximalIdeal_of_localHom_strictHens {A B : Type} [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B] (f : A →+* B) [IsLocalHom f] :
    (maximalIdeal B).comap f = maximalIdeal A := by
  ext x
  simp only [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff]

open IsLocalRing Polynomial in
open scoped TensorProduct in
private lemma locPiecesEtale_localization_atPrime {R A : Type} [CommRing R] [CommRing A]
    [Algebra R A] [Algebra.Etale R A] (q : Ideal A) [q.IsPrime] :
    _root_.GlobalTheory.LocAcyc.LocPiecesEtale R (Localization.AtPrime q) := by
  unfold _root_.GlobalTheory.LocAcyc.LocPiecesEtale
  exact ⟨Unit, inferInstance, inferInstance, inferInstance, fun _ => ⊤, monotone_const,
    fun _ => ⟨(), Algebra.mem_top⟩, fun _ => ⟨A, inferInstance, inferInstance, inferInstance, q,
      inferInstance, ⟨Subalgebra.topEquiv.symm⟩⟩⟩


open IsLocalRing Polynomial in
open scoped TensorProduct in
theorem _root_.GlobalTheory.strictHenselisation_etale_over_polynomial : ∀ (T E : Type) [CommRing T] [IsDomain T]
    [IsLocalRing T] [CommRing E]
    [Algebra (Polynomial T) E] [Algebra T E] [IsScalarTower T (Polynomial T) E]
    [Algebra.Etale (Polynomial T) E] (y : Ideal E) [y.IsPrime],
    ∃ (S : Type) (_ : CommRing S) (_ : IsLocalRing S) (_ : Algebra E S) (_ : Algebra T S)
      (_ : IsScalarTower T E S) (_ : Algebra (Polynomial T) S)
      (_ : IsScalarTower T (Polynomial T) S)
      (_ : IsScalarTower (Polynomial T) E S),
      (IsLocalRing.maximalIdeal S).comap (algebraMap E S) = y ∧ Module.Flat E S ∧
      _root_.GlobalTheory.LocAcyc.LocPiecesEtale E S ∧
      ∃ φ : Localization.AtPrime (y.comap (algebraMap (Polynomial T) E)) →+* S,
        φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) S ∧
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ := by
  intro T E _ _ _ _ _ _ _ _ y _
  obtain ⟨S, _, _, _, _, hsep, hflat, -, -, hpieces⟩ := _root_.GlobalTheory.exists_strictHenselisation
    (Localization.AtPrime y) (SeparableClosure (ResidueField (Localization.AtPrime y)))
  haveI := hsep
  have hP : _root_.GlobalTheory.LocAcyc.LocPiecesEtale (Localization.AtPrime y) S := hpieces
  letI : Algebra E S :=
    ((algebraMap (Localization.AtPrime y) S).comp (algebraMap E (Localization.AtPrime y))).toAlgebra
  letI : Algebra T S := ((algebraMap E S).comp (algebraMap T E)).toAlgebra
  letI : Algebra (Polynomial T) S := ((algebraMap E S).comp (algebraMap (Polynomial T) E)).toAlgebra
  haveI : IsScalarTower E (Localization.AtPrime y) S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower T E S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (Polynomial T) E S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower T (Polynomial T) S := IsScalarTower.of_algebraMap_eq fun x => by
    show algebraMap E S (algebraMap T E x) =
      algebraMap E S (algebraMap (Polynomial T) E (algebraMap T (Polynomial T) x))
    exact congrArg _ (IsScalarTower.algebraMap_apply T (Polynomial T) E x)
  haveI : IsScalarTower (Polynomial T) (Localization.AtPrime y) S :=
    IsScalarTower.of_algebraMap_eq fun x => by
      show algebraMap (Localization.AtPrime y) S (algebraMap E (Localization.AtPrime y)
          (algebraMap (Polynomial T) E x)) =
        algebraMap (Localization.AtPrime y) S (algebraMap (Polynomial T) (Localization.AtPrime y) x)
      exact congrArg _ (IsScalarTower.algebraMap_apply (Polynomial T) E (Localization.AtPrime y) x).symm
  have hcomap : (maximalIdeal S).comap (algebraMap E S) = y := by
    rw [IsScalarTower.algebraMap_eq E (Localization.AtPrime y) S, ← Ideal.comap_comap,
      _root_.GlobalTheory.comap_maximalIdeal_of_localHom_strictHens]
    exact Localization.AtPrime.under_maximalIdeal ..
  haveI : Module.Flat E (Localization.AtPrime y) := IsLocalization.flat _ y.primeCompl
  haveI := hflat
  have hflatE : Module.Flat E S := Module.Flat.trans E (Localization.AtPrime y) S
  have hpiecesE : _root_.GlobalTheory.LocAcyc.LocPiecesEtale E S :=
    _root_.GlobalTheory.indEtale_localPieces_trans E (Localization.AtPrime y) S
      (locPiecesEtale_localization_atPrime (R := E) (A := E) y) hP
  have hpiecesT : _root_.GlobalTheory.LocAcyc.LocPiecesEtale (Polynomial T) S :=
    _root_.GlobalTheory.indEtale_localPieces_trans (Polynomial T) (Localization.AtPrime y) S
      (locPiecesEtale_localization_atPrime (R := Polynomial T) (A := E) y) hP
  obtain ⟨P, _, φ, hφc, hφs⟩ := _root_.GlobalTheory.StrictHensUnion.isStrictHenselisation_of_directed_union T S hpiecesT
  have hPy : P = y.comap (algebraMap (Polynomial T) E) := by
    haveI : IsLocalHom φ := hφs.2.2.1
    calc P = ((maximalIdeal S).comap φ).comap (algebraMap (Polynomial T) (Localization.AtPrime P)) := by
          rw [_root_.GlobalTheory.comap_maximalIdeal_of_localHom_strictHens]
          exact (Localization.AtPrime.under_maximalIdeal ..).symm
      _ = (maximalIdeal S).comap (algebraMap (Polynomial T) S) := by
          rw [Ideal.comap_comap, hφc]
      _ = y.comap (algebraMap (Polynomial T) E) := by
          rw [IsScalarTower.algebraMap_eq (Polynomial T) E S, ← Ideal.comap_comap, hcomap]
  subst hPy
  exact ⟨S, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, hcomap, hflatE, hpiecesE, φ, hφc, hφs⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictHenselisationEtaleOverPolynomialStatement
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strictHenselisation_etale_over_polynomial_alt : ∀ (T E : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing E]
    [Algebra (Polynomial T) E] [Algebra T E] [IsScalarTower T (Polynomial T) E]
    [Algebra.Etale (Polynomial T) E] (y : Ideal E) [y.IsPrime],
    ∃ (S : Type) (_ : CommRing S) (_ : IsLocalRing S) (_ : Algebra E S) (_ : Algebra T S)
      (_ : IsScalarTower T E S) (_ : Algebra (Polynomial T) S) (_ : IsScalarTower T (Polynomial T) S)
      (_ : IsScalarTower (Polynomial T) E S),
      (IsLocalRing.maximalIdeal S).comap (algebraMap E S) = y ∧ Module.Flat E S ∧
      GlobalTheory.LocAcyc.LocPiecesEtale E S ∧
      ∃ φ : Localization.AtPrime (y.comap (algebraMap (Polynomial T) E)) →+* S,
        φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) S ∧
        GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ := by
  first | (exact @GlobalTheory.strictHenselisation_etale_over_polynomial) | (exact GlobalTheory.strictHenselisation_etale_over_polynomial) | (intros; apply GlobalTheory.strictHenselisation_etale_over_polynomial  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDetCharInvariantsLeSpanProdMaximalMinors
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CauchyBinetColumnFrameProdDetPowEqSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CauchyBinetColumnFrameProdDetPowEqSum
open Classical MvPolynomial

noncomputable section
namespace GlobalTheory.MinorFrame
open scoped Matrix
variable {ι : Type} [Fintype ι]

theorem eval_minorAt_frame {a d : ℕ} (x₀ : Var ι d a → ℂ) (τ : ι) (s : Fin a → Fin d) :
    eval x₀ (minorAt τ s) = ((Matrix.of fun (r : Fin d) (i : Fin a) => x₀ (τ, r, i)).submatrix s id).det := by
  unfold minorAt
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp

theorem rsub_frame_X {a d : ℕ} (x₀ : Var ι d a → ℂ) (τ : ι) (i j : Fin a) :
    rsub (frameMat x₀)ᴴ (X (τ, i, j)) = ∑ r : Fin d, C (star (x₀ (τ, r, i))) * (X (τ, r, j) : Pol ι d a) := by
  rw [rsub_X, Fintype.sum_prod_type, Finset.sum_eq_single τ]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_eq_single j]
    · simp [frameMat, Matrix.conjTranspose_apply]
    · intro b _ hb; simp [frameMat, Matrix.conjTranspose_apply, Ne.symm hb]
    · simp
  · intro b _ hb
    refine Finset.sum_eq_zero fun w _ => ?_
    simp [frameMat, Matrix.conjTranspose_apply, Ne.symm hb]
  · simp

end GlobalTheory.MinorFrame

noncomputable section
namespace GlobalTheory.MinorFrame
open scoped Matrix
variable {ι : Type} [Fintype ι]

theorem rsub_frame_det {a d : ℕ} (x₀ : Var ι d a → ℂ) (τ : ι) :
    rsub (frameMat x₀)ᴴ ((Matrix.of fun i j : Fin a => (X (τ, i, j) : MvPolynomial (ι × Fin a × Fin a) ℂ)).det) =
      ∑ s : {s : Fin a → Fin d // StrictMono s}, C (star (eval x₀ (minorAt τ s.1))) * minorAt τ s.1 := by
  rw [AlgHom.map_det]
  set A : Matrix (Fin d) (Fin a) ℂ := Matrix.of fun (r : Fin d) (i : Fin a) => x₀ (τ, r, i) with hA
  have hM : (rsub (frameMat x₀)ᴴ : MvPolynomial (ι × Fin a × Fin a) ℂ →ₐ[ℂ] Pol ι d a).mapMatrix
      (Matrix.of fun i j : Fin a => (X (τ, i, j) : MvPolynomial (ι × Fin a × Fin a) ℂ)) =
      (Aᴴ.map (C : ℂ →+* Pol ι d a)) * xMat τ d a := by
    ext i j
    simp [rsub_frame_X, xMat, Matrix.mul_apply, hA, Matrix.conjTranspose_apply]
  rw [hM, det_mul_eq_sum_sm]
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 1
  · rw [eval_minorAt_frame, ← hA, Matrix.submatrix_map, ← Matrix.det_conjTranspose, Matrix.conjTranspose_submatrix]
    exact (RingHom.map_det _ _).symm

theorem rsub_frame_detG {a d : ℕ} (n : ι → ℕ) (x₀ : Var ι d a → ℂ) :
    rsub (frameMat x₀).conjTranspose (detG a n) =
      ∑ T : Tup ι a d n, star (eval x₀ (prodMinors T)) • prodMinors T := by
  unfold detG
  simp only [map_prod, map_pow, rsub_frame_det]
  rw [Finset.prod_congr rfl fun τ _ => (Fin.prod_const (n τ) _).symm]
  rw [Finset.prod_congr rfl fun τ _ => Fintype.prod_sum _, Fintype.prod_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  unfold prodMinors
  simp only [map_prod, star_prod, smul_eq_C_mul, Finset.prod_mul_distrib]

end GlobalTheory.MinorFrame

namespace GlobalTheory.MinorFrame

theorem rsub_frame_detG_eq_sum : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ) (x₀ : Var ι d a → ℂ),
    rsub (frameMat x₀).conjTranspose (detG a n) =
      ∑ T : Tup ι a d n, star (MvPolynomial.eval x₀ (prodMinors T)) • prodMinors T :=
  fun _ _ n x₀ => rsub_frame_detG n x₀

end GlobalTheory.MinorFrame
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CauchyBinetColumnFrameProdDetPowEqSumStatement
open Classical MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cauchyBinet_columnFrame_prodDetPow_eq_sum : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ) (x₀ : GlobalTheory.MinorFrame.Var ι d a → ℂ), GlobalTheory.MinorFrame.rsub (GlobalTheory.MinorFrame.frameMat x₀).conjTranspose (GlobalTheory.MinorFrame.detG a n) = ∑ T : GlobalTheory.MinorFrame.Tup ι a d n, star (MvPolynomial.eval x₀ (GlobalTheory.MinorFrame.prodMinors T)) • GlobalTheory.MinorFrame.prodMinors T := by
  first | exact @GlobalTheory.MinorFrame.rsub_frame_detG_eq_sum | exact GlobalTheory.MinorFrame.rsub_frame_detG_eq_sum | (intros; apply GlobalTheory.MinorFrame.rsub_frame_detG_eq_sum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPairingLinearSubstitutionAdjoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPairingLinearSubstitutionAdjoint
noncomputable section

open MvPolynomial Matrix Formalism.L2.DIV

namespace GlobalTheory.MinorFrame

variable {σ σ' : Type} [Fintype σ] [Fintype σ']

theorem constantCoeff_rsub (M : Matrix σ' σ ℂ) (g : MvPolynomial σ ℂ) :
    constantCoeff (rsub M g) = constantCoeff g := by
  have : (constantCoeff : MvPolynomial σ' ℂ →+* ℂ).comp (rsub M).toRingHom = constantCoeff := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp
    · intro i; simp [rsub_X]
  exact congrArg (fun φ : MvPolynomial σ ℂ →+* ℂ => φ g) this

theorem pderiv_rsub [DecidableEq σ] [DecidableEq σ'] (M : Matrix σ' σ ℂ) (s : σ') (g : MvPolynomial σ ℂ) :
    pderiv s (rsub M g) = ∑ w, C (M s w) * rsub M (pderiv w g) := by
  induction g using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p k hp =>
    have hX : pderiv s (rsub M (X k)) = C (M s k) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [rsub_X, map_sum, Finset.sum_eq_single s]
      · simp [pderiv_X]
      · intro b _ hb
        rw [Derivation.leibniz, pderiv_C, pderiv_X_of_ne hb]
        simp
      · simp
    rw [map_mul, Derivation.leibniz, hX, hp, smul_eq_mul, smul_eq_mul]
    simp_rw [Derivation.leibniz, smul_eq_mul, map_add (f := _), map_mul, mul_add, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_eq_single k]
      · rw [pderiv_X_self, map_one]; ring
      · intro b _ hb
        rw [pderiv_X_of_ne hb.symm]
        simp
      · simp
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring

theorem fockL_rsub_adj (M : Matrix σ' σ ℂ) (F : MvPolynomial σ ℂ) (F' : MvPolynomial σ' ℂ) :
    fockL (rsub M F) F' = fockL F (rsub Mᴴ F') := by
  classical
  induction F using MvPolynomial.induction_on generalizing F' with
  | C a => rw [algHom_C, algebraMap_eq, fockL_C_left, fockL_C_left, constantCoeff_rsub]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, hp, hq]
  | mul_X p v hp =>
    have e1 : rsub M (p * X v) = ∑ w, M w v • (X w * rsub M p) := by
      rw [map_mul, rsub_X, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_eq_C_mul]; ring
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, map_sum, LinearMap.sum_apply]
    simp_rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, fockL_X_pderiv, hp]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [mul_comm p, fockL_X_pderiv, pderiv_rsub, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← smul_eq_C_mul, map_smul, Matrix.conjTranspose_apply, starRingEnd_apply]

theorem fockS_rsub_adj : ∀ {σ σ' : Type} [Fintype σ] [Fintype σ'] (M : Matrix σ' σ ℂ) (F : MvPolynomial σ ℂ)
    (F' : MvPolynomial σ' ℂ), Formalism.L2.DIV.fockS (GlobalTheory.MinorFrame.rsub M F) F' =
      Formalism.L2.DIV.fockS F (GlobalTheory.MinorFrame.rsub M.conjTranspose F') := by
  intro σ σ' _ _ M F F'
  exact fockL_rsub_adj M F F'

end GlobalTheory.MinorFrame

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPairingLinearSubstitutionAdjointStatement
open Classical MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockPairing_linearSubstitution_adjoint : ∀ {σ σ' : Type} [Fintype σ] [Fintype σ'] (M : Matrix σ' σ ℂ) (F : MvPolynomial σ ℂ) (F' : MvPolynomial σ' ℂ), Formalism.L2.DIV.fockS (GlobalTheory.MinorFrame.rsub M F) F' = Formalism.L2.DIV.fockS F (GlobalTheory.MinorFrame.rsub M.conjTranspose F') := by
  first | exact @GlobalTheory.MinorFrame.fockS_rsub_adj | exact GlobalTheory.MinorFrame.fockS_rsub_adj | (intros; apply GlobalTheory.MinorFrame.fockS_rsub_adj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDetCharInvariantsLeSpanProdMaximalMinors
open Classical MvPolynomial

noncomputable section

namespace GlobalTheory.MinorFrame

variable {ι : Type} [Fintype ι]

theorem eval_rsub_frameMat {a d : ℕ} (x₀ : Var ι d a → ℂ) (g : ι → Matrix (Fin a) (Fin a) ℂ) (P : Pol ι d a) :
    eval (fun v : ι × Fin a × Fin a => g v.1 v.2.1 v.2.2) (rsub (frameMat x₀) P) = eval x₀ (colSub g P) := by
  have h : (eval (fun v : ι × Fin a × Fin a => g v.1 v.2.1 v.2.2)).comp
        (rsub (frameMat x₀) : Pol ι d a →ₐ[ℂ] _).toRingHom
      = (eval x₀).comp (colSub g : Pol ι d a →ₐ[ℂ] Pol ι d a).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp
    · intro v
      obtain ⟨τ, r, j⟩ := v
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, rsub_X, colSub, aeval_X,
        map_sum, map_mul, eval_C, eval_X]
      rw [Fintype.sum_prod_type, Finset.sum_eq_single τ]
      · rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_eq_single j]
        · simp [frameMat, mul_comm]
        · intro b _ hb; simp [frameMat, hb]
        · simp
      · intro b _ hb; simp [frameMat, hb]
      · simp
  exact congrArg (fun φ : Pol ι d a →+* ℂ => φ P) h

theorem rsub_frameMat_of_mem_inv {a d : ℕ} {n : ι → ℕ} (x₀ : Var ι d a → ℂ) {P : Pol ι d a}
    (hP : P ∈ inv a d n) : rsub (frameMat x₀) P = eval x₀ P • detG a n := by
  rw [← sub_eq_zero]
  apply GlobalTheory.T.unitaryGroup_family_zariski_dense
  intro g
  rw [map_sub, eval_rsub_frameMat x₀ (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) P, hP g, smul_eval, smul_eval,
    eval_detG a n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ))]
  ring

theorem inv_le_span_prodMinors : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ), GlobalTheory.MinorFrame.inv a d n ≤ Submodule.span ℂ (Set.range (GlobalTheory.MinorFrame.prodMinors (ι := ι) (a := a) (d := d) (n := n))) := by
  intro ι _ a d n P hP
  set c := Formalism.L2.DIV.fockS (detG (ι := ι) a n) (detG a n) with hc
  have hc0 : c ≠ 0 := fun h => by
    have := fockS_self_re_pos (detG_ne_zero (ι := ι) a n)
    rw [← hc, h] at this
    simp at this
  have key : c • P = ∑ T : Tup ι a d n, Formalism.L2.DIV.fockS (prodMinors T) P • prodMinors T := by
    apply MvPolynomial.funext
    intro x₀
    have h1 := GlobalTheory.T.fockPairing_linearSubstitution_adjoint (frameMat x₀).conjTranspose (detG a n) P
    rw [Matrix.conjTranspose_conjTranspose, rsub_frameMat_of_mem_inv x₀ hP, GlobalTheory.T.cauchyBinet_columnFrame_prodDetPow_eq_sum] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Formalism.L2.DIV.fockL_apply, ← Formalism.L2.DIV.fockL_apply, map_sum, map_smul, LinearMap.sum_apply] at h1
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, Formalism.L2.DIV.fockL_apply, smul_eq_mul,
      starRingEnd_apply, star_star] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [smul_eval, map_sum]
    simp only [smul_eval]
    rw [mul_comm, ← h1]
    refine Finset.sum_congr rfl fun T _ => ?_
    ring
  have hP' : P = c⁻¹ • ∑ T : Tup ι a d n, Formalism.L2.DIV.fockS (prodMinors T) P • prodMinors T := by
    rw [← key, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [hP']
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun T _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨T, rfl⟩))

end GlobalTheory.MinorFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDetCharInvariantsLeSpanProdMaximalMinorsStatement
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockDetCharInvariants_le_span_prodMaximalMinors : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ), GlobalTheory.MinorFrame.inv a d n ≤ Submodule.span ℂ (Set.range (GlobalTheory.MinorFrame.prodMinors (ι := ι) (a := a) (d := d) (n := n))) := by
  first | exact @GlobalTheory.MinorFrame.inv_le_span_prodMinors | exact GlobalTheory.MinorFrame.inv_le_span_prodMinors | (intros; apply GlobalTheory.MinorFrame.inv_le_span_prodMinors <;> assumption)
end
end
