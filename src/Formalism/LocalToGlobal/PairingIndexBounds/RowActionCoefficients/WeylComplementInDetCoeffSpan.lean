module

public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.CardFilterValLt
public import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.FormCoreSK

@[expose] public section

section -- merged from Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.ColHLe
open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.L2.G.Model.TS Formalism.L2.G.Pend

def hvE {A : Type*} [CommRing A] {n : ℕ} (x : Fin n → ℕ → A) (y : Matrix (Fin n) (Fin n) A) (c : ℕ) (h : Fin c → ℕ)
    (hh : ∀ k, h k ≤ n) : A :=
  ∏ k, (Matrix.of fun i t : Fin (h k) => ∑ a, x a i.val * y a (Fin.castLE (hh k) t)).det

def hvO {A : Type*} [CommRing A] {n : ℕ} (x : Fin n → ℕ → A) (y : Matrix (Fin n) (Fin n) A) (c : ℕ) (h : Fin c → ℕ) : A :=
  ∏ k, (catM (h k) y x).det

def colH {n : ℕ} (ν : Fin n → ℕ) (k : ℕ) : ℕ := (Finset.univ.filter fun t : Fin n => k < ν t).card

theorem colH_le {n : ℕ} (ν : Fin n → ℕ) (k : ℕ) : colH ν k ≤ n := by
  unfold colH
  calc (Finset.univ.filter fun t : Fin n => k < ν t).card ≤ (Finset.univ : Finset (Fin n)).card :=
        Finset.card_filter_le _ _
    _ = n := by simp

abbrev GenR (R : Type*) [CommRing R] (n : ℕ) : Type _ := MvPolynomial (ℕ × Fin n) (MvPolynomial (Fin n × Fin n) R)

def gX (R : Type*) [CommRing R] (n : ℕ) : Fin n → ℕ → GenR R n := fun a i => X (i, a)

def gY (R : Type*) [CommRing R] (n : ℕ) : Matrix (Fin n) (Fin n) (GenR R n) := fun a t => C (X (a, t))

def yV (R : Type*) [CommRing R] (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) R) := fun a t => X (a, t)

def unitM (R : Type*) [CommRing R] {n m : ℕ} (I : Fin m → Fin n) : Matrix (Fin n) (Fin n) R :=
  fun a t => if h : t.val < m then (if a = I ⟨t.val, h⟩ then 1 else 0) else 0

end Formalism.L2.PairingIndexBounds.Ent
end
end

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.L2.G.Model.TS Formalism.L2.G.Pend

def WeylLatticeInDetCoeffSpan : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (ν : Fin n → ℕ), Antitone ν → ∀ c e : ℕ, (∀ t, ν t ≤ c) →
    weyl R n n le_rfl ν ≤ Submodule.span R (Set.range fun m : ℕ × Fin n →₀ ℕ =>
      AddMonoidAlgebra.coeff ((Matrix.of fun a i : Fin n => gX R n a i.val).det ^ e *
        hvE (gX R n) (gY R n) c (fun k => colH ν k.val) (fun k => colH_le ν k.val)) m)

def WeylComplementInDetCoeffSpan : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (μ : Fin n → ℕ), Antitone μ → ∀ c : ℕ, (∀ t, μ t ≤ c) →
    weyl R n n le_rfl (fun t => c - μ t.rev) ≤ Submodule.span R (Set.range fun m : ℕ × Fin n →₀ ℕ =>
      AddMonoidAlgebra.coeff (hvO (gX R n) (gY R n) c (fun k => colH μ k.val)) m)

def PairE : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (ν : Fin n → ℕ), Antitone ν → ∀ c : ℕ, (∀ t, ν t ≤ c) →
    ∀ (x : Fin n → ℕ → K), ∀ Q ∈ dualWeyl K n n ν,
      fockR (hvE (fun a i => C (x a i)) (yV K n) c (fun k => colH ν k.val) (fun k => colH_le ν k.val)) Q =
        eval (fun v : Fin n × Fin n => x v.1 v.2.val) Q * fockR (hw K le_rfl ν) (hw K le_rfl ν)

def PairO : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (μ : Fin n → ℕ), Antitone μ → ∀ c : ℕ, (∀ t, μ t ≤ c) →
    ∀ (x : Fin n → ℕ → K) (I : ∀ k : Fin c, Fin (n - colH μ k.val) → Fin n),
      fockR (hvO (fun a i => C (x a i)) (yV K n) c (fun k => colH μ k.val))
          (bideterminant K (fun k : Fin c => n - colH μ k.val) (fun _ => Nat.sub_le _ _) I) =
        (∏ k : Fin c, (catM (colH μ k.val) (unitM K (I k)) x).det) *
          fockR (hw K le_rfl fun t : Fin n => c - μ t.rev) (hw K le_rfl fun t : Fin n => c - μ t.rev)

def Reorder : Prop :=
  ∀ (B : Type) [CommRing B] (r n : ℕ) (K K' : ℕ) (sz : Fin K → ℕ) (sz' : Fin K' → ℕ) (hsz : ∀ k, sz k ≤ n) (hsz' : ∀ k, sz' k ≤ n),
    (shapeDeg sz : Fin n → ℕ) = shapeDeg sz' → ∀ I : ∀ k, Fin (sz k) → Fin r,
      ∃ I' : ∀ k, Fin (sz' k) → Fin r, bideterminant B sz hsz I = bideterminant B sz' hsz' I'

def ShapeE : Prop :=
  ∀ (n : ℕ) (ν : Fin n → ℕ), Antitone ν → ∀ c : ℕ, (∀ t, ν t ≤ c) → (shapeDeg fun k : Fin c => colH ν k.val) = ν

def ShapeO : Prop :=
  ∀ (n : ℕ) (μ : Fin n → ℕ), Antitone μ → ∀ c : ℕ, (∀ t, μ t ≤ c) →
    (shapeDeg fun k : Fin c => n - colH μ k.val) = fun t : Fin n => c - μ t.rev

def DualBases : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field K] [Algebra O K] [IsFractionRing O K] [CharZero K]
    (n : ℕ) (ν : Fin n → ℕ), Antitone ν →
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (e e' : ι → MvPolynomial (Fin n × Fin n) K),
      (∀ i, e i ∈ (weyl O n n le_rfl ν).map (toK O K)) ∧ (∀ i, e' i ∈ (dualWeyl O n n ν).map (toK O K)) ∧
      (∀ i k, fockR (e i) (e' k) = if i = k then fockR (hw K le_rfl ν) (hw K le_rfl ν) else 0) ∧
      dualWeyl K n n ν ≤ Submodule.span K (Set.range e)

def FockProd : Prop :=
  ∀ (K B σ τ : Type) [CommRing K] [Fintype B] (em : B → σ → τ), (Function.Injective fun x : B × σ => em x.1 x.2) →
    ∀ F G : B → MvPolynomial σ K,
      fockR (∏ b, rename (em b) (F b)) (∏ b, rename (em b) (G b)) = ∏ b, fockR (F b) (G b)

def Interp : Prop :=
  ∀ (K τ W : Type) [Field K] [Infinite K] [AddCommGroup W] [Module K W] (S : Finset (τ →₀ ℕ)) (w : (τ →₀ ℕ) → W),
    (∀ x : τ → K, ∑ m ∈ S, (m.prod fun t k => x t ^ k) • w m = 0) → ∀ m ∈ S, w m = 0

end Formalism.L2.PairingIndexBounds.Ent
