module

public import Mathlib

@[expose] public section

section -- merged from Formalism.LocalToGlobal.CharacterGerms.GeNatCast
namespace Formalism.L2.FormalSeriesBounds

open Finset

noncomputable section

structure VF (C : Type*) [Field C] where
  v : AddValuation C (WithTop ℝ)
  l : ℕ
  l_prime : l.Prime
  v_l : v (l : C) = 1

variable {C : Type*} [Field C]

namespace VF

variable (V : VF C)

def Ge (w : ℝ) (a : C) : Prop := (w : WithTop ℝ) ≤ V.v a

variable {V}

theorem Ge.mono {w w' : ℝ} {a : C} (h : V.Ge w a) (hw : w' ≤ w) : V.Ge w' a := le_trans (WithTop.coe_le_coe.mpr hw) h

theorem Ge.zero (w : ℝ) : V.Ge w (0 : C) := by
  show ((w : ℝ) : WithTop ℝ) ≤ V.v 0
  rw [AddValuation.map_zero]
  exact le_top

theorem Ge.add {w : ℝ} {a b : C} (ha : V.Ge w a) (hb : V.Ge w b) : V.Ge w (a + b) := le_trans (le_min ha hb) (V.v.map_add a b)

theorem Ge.neg {w : ℝ} {a : C} (ha : V.Ge w a) : V.Ge w (-a) := by
  show ((w : ℝ) : WithTop ℝ) ≤ V.v (-a)
  rw [AddValuation.map_neg]
  exact ha

theorem Ge.sub {w : ℝ} {a b : C} (ha : V.Ge w a) (hb : V.Ge w b) : V.Ge w (a - b) := by
  rw [sub_eq_add_neg]
  exact Ge.add ha (Ge.neg hb)

theorem Ge.sum {ι : Type*} {s : Finset ι} {f : ι → C} {w : ℝ} (h : ∀ i ∈ s, V.Ge w (f i)) :
    V.Ge w (∑ i ∈ s, f i) := Finset.sum_induction f (fun x => V.Ge w x) (fun _ _ ha hb => Ge.add ha hb) (Ge.zero w) h

theorem Ge.mul {w w' : ℝ} {a b : C} (ha : V.Ge w a) (hb : V.Ge w' b) : V.Ge (w + w') (a * b) := by
  show ((w + w' : ℝ) : WithTop ℝ) ≤ V.v (a * b)
  rw [AddValuation.map_mul, WithTop.coe_add]
  exact add_le_add ha hb

theorem Ge.one : V.Ge 0 (1 : C) := by
  show ((0 : ℝ) : WithTop ℝ) ≤ V.v 1
  rw [AddValuation.map_one]
  exact le_of_eq WithTop.coe_zero

theorem Ge.pow {a : C} (ha : V.Ge 0 a) (n : ℕ) : V.Ge 0 (a ^ n) := by
  induction n with
  | zero => simpa using (Ge.one (V := V))
  | succ n ih =>
    rw [pow_succ]
    simpa using Ge.mul ih ha

theorem Ge.mul_int {w : ℝ} {a b : C} (ha : V.Ge 0 a) (hb : V.Ge w b) : V.Ge w (a * b) := by
  simpa using Ge.mul ha hb

theorem ge_l : V.Ge 1 (V.l : C) := (le_of_eq WithTop.coe_one).trans V.v_l.symm.le

theorem l_ne_zero : (V.l : C) ≠ 0 := by
  intro h
  have h1 := V.v_l
  rw [h, AddValuation.map_zero] at h1
  simp at h1

theorem ge_natCast (n : ℕ) : V.Ge 0 (n : C) := by
  induction n with
  | zero => rw [Nat.cast_zero]; exact Ge.zero 0
  | succ n ih => rw [Nat.cast_succ]; exact Ge.add ih Ge.one

theorem Ge.of_l_mul {w : ℝ} {a : C} (h : V.Ge w ((V.l : C) * a)) : V.Ge (w - 1) a := by
  have h0 : ((w : ℝ) : WithTop ℝ) ≤ 1 + V.v a := by
    have h2 : ((w : ℝ) : WithTop ℝ) ≤ V.v ((V.l : C) * a) := h
    rwa [AddValuation.map_mul, V.v_l] at h2
  show (((w - 1) : ℝ) : WithTop ℝ) ≤ V.v a
  by_cases hva : V.v a = ⊤
  · rw [hva]; exact le_top
  · obtain ⟨x, hx⟩ := WithTop.ne_top_iff_exists.mp hva
    rw [← hx] at h0 ⊢
    have h' : w ≤ 1 + x := by exact_mod_cast h0
    exact WithTop.coe_le_coe.mpr (by linarith)

theorem Ge.l_mul {w : ℝ} {a : C} (h : V.Ge w a) : V.Ge (1 + w) ((V.l : C) * a) := by
  show ((1 + w : ℝ) : WithTop ℝ) ≤ V.v ((V.l : C) * a)
  rw [AddValuation.map_mul, V.v_l, WithTop.coe_add, WithTop.coe_one]
  exact add_le_add le_rfl h

theorem Ge.l_inv_mul {w : ℝ} {a : C} (h : V.Ge w a) : V.Ge (w - 1) ((V.l : C)⁻¹ * a) := by
  apply Ge.of_l_mul
  rwa [← mul_assoc, mul_inv_cancel₀ l_ne_zero, one_mul]

end VF

section Ops

variable {N : Type*}

def teich (l : ℕ) (c : C) (x : ℕ → N → C) : ℕ → N → C := fun i n => c ^ (l ^ i) * x i n

def Vpow (s : ℕ) (x : ℕ → N → C) : ℕ → N → C := fun i n => if i < s then 0 else x (i - s) n

def Fs (l : ℕ) (x : ℕ → N → C) : ℕ → N → C := fun i n => (l : C) * x (i + 1) n

def sumV (y : ℕ → ℕ → N → C) : ℕ → N → C := fun i n => ∑ s ∈ range (i + 1), y s (i - s) n

def const0 (h : N → C) : ℕ → N → C := fun i n => if i = 0 then h n else 0

end Ops

structure Cart (V : VF C) (d : ℕ) (I J : Type*) where

  ty : I ⊕ J → ZMod d
  Ty : AddSubgroup (ℕ → I ⊕ J → C)
  teich_mem : ∀ c, V.Ge 0 c → ∀ x ∈ Ty, teich V.l c x ∈ Ty
  V_mem : ∀ x ∈ Ty, Vpow 1 x ∈ Ty
  F_mem : ∀ x ∈ Ty, Fs V.l x ∈ Ty
  sumV_mem : ∀ y : ℕ → ℕ → I ⊕ J → C, (∀ s, y s ∈ Ty) → sumV y ∈ Ty

  t2 : ∀ x ∈ Ty, ∀ s, (∀ i < s, x i = 0) → ∀ n, V.Ge 0 (x s n)

  t3 : ∀ ζ : J → C, (∀ j, V.Ge 0 (ζ j)) → const0 (Sum.elim 0 ζ) ∈ Ty

  t4 : ∀ (a : ZMod d) (u : I → C), (∀ c, V.Ge 0 (u c)) → (∀ c, ty (Sum.inl c) ≠ a → u c = 0) →
    ∃ x ∈ Ty, x 0 = Sum.elim u 0 ∧ ∀ (i : ℕ) n, ty n ≠ a + i → x i n = 0

end

end Formalism.L2.FormalSeriesBounds
end

section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTiePSplitDef
namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePSplit

open Polynomial

def SplitSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (O : Type) [CommRing O] (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (M : O →+* Matrix (Fin n) (Fin n) C) (P : Matrix (Fin n) (Fin n) C) (em : ι → (O →+* C)),
    P * P = P → (∀ x, P * M x = M x * P) → Function.Injective em →
    (∀ x, Polynomial.aeval (M x) (∏ c, (X - Polynomial.C (em c x))) * P = 0) →
    ∀ v : Fin n → C, ∃ w : ι → (Fin n → C), Matrix.mulVec P v = ∑ c, w c ∧ ∀ c x, Matrix.mulVec (M x) (w c) = em c x • w c

end RowTiePSplit

end Formalism.L2.FormalSeriesBounds
end

section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTieUpFBrPl
set_option autoImplicit false

noncomputable section

open TensorProduct IsLocalRing

namespace Formalism.L2.FormalSeriesBounds.UpFBr.Pl

def tauX {l : ℕ} [Fact l.Prime] {OE : Type} [CommRing OE] {R : Type} [CommRing R] [Algebra ℤ_[l] R] (τ : OE →+* R) :
    (ℤ_[l] ⊗[ℤ] OE) →ₐ[ℤ_[l]] R :=
  Algebra.TensorProduct.lift (Algebra.ofId ℤ_[l] R) τ.toIntAlgHom (fun _ _ => Commute.all _ _)

def EmbX {l : ℕ} [Fact l.Prime] {OE : Type} [CommRing OE] {R : Type} [CommRing R] [Algebra ℤ_[l] R]
    (e : ℤ_[l] ⊗[ℤ] OE) : Set (OE →+* R) := {τ | tauX τ e = 1}

def PlaceX (l : ℕ) [Fact l.Prime] (OE : Type) [CommRing OE] (R : Type) [CommRing R] [Algebra ℤ_[l] R] (d : ℕ)
    (em : ZMod d → OE →+* R) : Prop :=
  ∃ e : ℤ_[l] ⊗[ℤ] OE, e * e = e ∧ e ≠ 0 ∧ (∀ f : ℤ_[l] ⊗[ℤ] OE, f * f = f → f * e = f → f = 0 ∨ f = e) ∧
    ∃ (_ : NeZero (Module.finrank ℤ_[l] (LinearMap.range (LinearMap.mulLeft ℤ_[l] e))))
      (t : Fin (Module.finrank ℤ_[l] (LinearMap.range (LinearMap.mulLeft ℤ_[l] e))) ≃ EmbX (R := R) e)
      (jj : ZMod d ≃ Fin (Module.finrank ℤ_[l] (LinearMap.range (LinearMap.mulLeft ℤ_[l] e)))),
      (∀ a, jj (a + 1) = jj a + 1) ∧ (∀ a, ((t (jj a) : EmbX (R := R) e) : OE →+* R) = em a) ∧
      ∃ b : Module.Basis (Fin (Module.finrank ℤ_[l] (LinearMap.range (LinearMap.mulLeft ℤ_[l] e)))) ℤ_[l]
          (LinearMap.range (LinearMap.mulLeft ℤ_[l] e)),
        IsUnit (Matrix.det (Matrix.of fun i j =>
          tauX ((t j : EmbX (R := R) e) : OE →+* R) (b i : ℤ_[l] ⊗[ℤ] OE)))

def PlaceCriterionOfIdempotent : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE]
    [Module.Finite ℤ OE] (R : Type) [CommRing R] [IsDomain R] [CharZero R] [IsLocalRing R] [Algebra ℤ_[l] R],
    (l : R) ∈ maximalIdeal R → ¬ ((l : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ OE)) →
    ∀ (d : ℕ) [NeZero d] (em : ZMod d → OE →+* R),
      (∀ a x, em (a + 1) x - em a x ^ l ∈ maximalIdeal R) →
      (∀ a a', a ≠ a' → ∃ x, em a x - em a' x ∉ maximalIdeal R) →
      (∃ ε : OE, (∃ y, ε * ε - ε = (l : OE) * y) ∧ (∀ a, em a ε - 1 ∈ maximalIdeal R) ∧
        ∀ x : OE, (∀ a, em a x ∈ maximalIdeal R) → ∃ y, ε * x = (l : OE) * y) → PlaceX l OE R d em

end Formalism.L2.FormalSeriesBounds.UpFBr.Pl
end
end

section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyJointDef
namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePKey

def JointEigSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C], IsAlgClosed C → ∀ (n q : ℕ), 2 ≤ q →
    ∀ (T : Set (Matrix (Fin n) (Fin n) C)), (∀ t ∈ T, t ^ q = t) → (∀ s ∈ T, ∀ t ∈ T, s * t = t * s) →
    ∀ v : Fin n → C, ∃ (m : ℕ) (w : Fin m → Fin n → C), v = ∑ j, w j ∧
      ∀ j, ∀ t ∈ T, ∃ c : C, Matrix.mulVec t (w j) = c • w j

end RowTiePKey

end Formalism.L2.FormalSeriesBounds
end
