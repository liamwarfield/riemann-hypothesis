module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.CoreSt

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.PairSym
noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def EtaLt (r : Sym m n) (N : ℕ) : Prop := ∀ t ∈ r.support, (∑ k, t (Sum.inr k)) < N

def EtaLe (r : Sym m n) (N : ℕ) : Prop := ∀ t ∈ r.support, (∑ k, t (Sum.inr k)) ≤ N

def vecVar (ε : Fin m → Bool) (a : Fin m) (i : Fin n) : Sym m n :=
  if ε a then X (Sum.inl (a, i, false)) else X (Sum.inr (a, i, true))

def covVar (ε : Fin m → Bool) (b : Fin m) (i : Fin n) : Sym m n :=
  if ε b then X (Sum.inr (b, i, false)) else X (Sum.inl (b, i, true))

def pairSym (ε : Fin m → Bool) (a b : Fin m) : Sym m n := ∑ i, vecVar ε a i * covVar ε b i

def CompSt : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (u v : Sym m n) (d₁ d₂ : ℕ), SymbolInFirstFamily ε u → SymbolInFirstFamily ε v → EtaLe u d₁ → EtaLe v d₂ →
    ∃ r : Sym m n, SymbolInFirstFamily ε r ∧ EtaLt r (d₁ + d₂) ∧ ∀ f, op u (op v f) = op (u * v) f + op r f

def FFTSym : Prop :=
  PositivityTheory.Rg.Sw.FFT → ∀ (m n : ℕ) (ε : Fin m → Bool) (s : Sym m n), SymbolInFirstFamily ε s → (∀ i j, symK ε i j s = 0) →
    s ∈ Algebra.adjoin ℂ (Set.range fun ab : Fin m × Fin m => (pairSym (n := n) ε ab.1 ab.2))

end PositivityTheory.Rg.Sw.LC
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.ZeroRight
noncomputable section

namespace PositivityTheory.Rg.Sw.LC

namespace CoreA

variable {V : Type} [AddCommGroup V] [Module ℂ V]

structure PosH (φ : V → V → ℂ) : Prop where
  add : ∀ v, ∀ w₁ w₂, φ v (w₁ + w₂) = φ v w₁ + φ v w₂
  smul : ∀ v w (r : ℂ), φ v (r • w) = r * φ v w
  herm : ∀ v w, φ w v = star (φ v w)
  pos : ∀ v, v ≠ 0 → 0 < (φ v v).re

variable {φ : V → V → ℂ}

namespace PosH

variable (h : PosH φ)
include h

theorem zero_right (v : V) : φ v 0 = 0 := by
  have := h.smul v 0 0
  simpa using this

theorem zero_left (v : V) : φ 0 v = 0 := by
  rw [h.herm v 0, h.zero_right, star_zero]

theorem add_left (v₁ v₂ w : V) : φ (v₁ + v₂) w = φ v₁ w + φ v₂ w := by
  rw [h.herm w (v₁ + v₂), h.add, star_add, ← h.herm w v₁, ← h.herm w v₂]

theorem smul_left (v w : V) (r : ℂ) : φ (r • v) w = star r * φ v w := by
  rw [h.herm w (r • v), h.smul, star_mul', ← h.herm w v]

theorem sum_left {ι : Type*} (s : Finset ι) (c : ι → ℂ) (b : ι → V) (w : V) :
    φ (∑ k ∈ s, c k • b k) w = ∑ k ∈ s, star (c k) * φ (b k) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [h.zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, h.add_left, h.smul_left, ih]

theorem definite (v : V) (hv : φ v v = 0) : v = 0 := by
  by_contra hne
  have := h.pos v hne
  rw [hv] at this
  simp at this

theorem re_nonneg (v : V) : 0 ≤ (φ v v).re := by
  by_cases hv : v = 0
  · subst hv; simp [h.zero_right]
  · exact (h.pos v hv).le

def perp (W : Submodule ℂ V) : Submodule ℂ V where
  carrier := {v | ∀ w ∈ W, φ w v = 0}
  add_mem' := by
    intro a b ha hb w hw
    rw [h.add, ha w hw, hb w hw, add_zero]
  zero_mem' := fun w _ => h.zero_right w
  smul_mem' := by
    intro r v hv w hw
    rw [h.smul, hv w hw, mul_zero]

theorem inf_perp (W : Submodule ℂ V) : W ⊓ h.perp W = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rcases Submodule.mem_inf.1 hv with ⟨h1, h2⟩
  exact (Submodule.mem_bot ℂ).2 (h.definite v (h2 v h1))

end PosH

end CoreA

end PositivityTheory.Rg.Sw.LC
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.EquivLift
noncomputable section

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw

def EquivLift : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c : ℝ), 0 < c → ∀ (R : Finset (Fin m → ℕ)) (t : Module.End ℂ (PX m n)),
    (∀ f ∈ box ε (R : Set _), t f ∈ box ε (R : Set _)) →
    (∀ i j, ∀ f ∈ box ε (R : Set _), t (KopL ε i j f) = KopL ε i j (t f)) →
    ∃ w ∈ Algebra.adjoin ℂ (Set.range fun ab : Fin m × Fin m => firstFamilyOperatorEnd (n := n) ε c ab.1 ab.2), ∀ f ∈ box ε (R : Set _), t f = w f

end PositivityTheory.Rg.Sw.LC
end
end
