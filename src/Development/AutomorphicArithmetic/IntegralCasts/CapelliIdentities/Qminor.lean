module

public import Mathlib

@[expose] public section

/-!
# Quantum Minors, Quantum Determinant, and `𝔤𝔩₂` Casimir Action

Defines the `𝔤𝔩ₙ` commutation relations (`GlRel`), the shifted generator matrix `Tm`,
quantum minors (`qminor`) and quantum determinant (`qdet`), and evaluates `qdet E (u + 1/2)`
on a weight-`k` lowest/highest-weight vector `φ` of a `𝔤𝔩₂`-module (the Casimir eigenvalue
`(u + (k - 1)/2)(u - (k - 1)/2)`).
-/

noncomputable def UpperTheory.Reformulated.B.Qf10.GlRel.{u_1}
    {A : Type u_1} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) : Prop :=
  ∀ a b c d : Fin n,
    E a b * E c d - E c d * E a b =
      (if b = c then E a d else 0) - (if d = a then E c b else 0)

noncomputable def UpperTheory.Reformulated.B.Qf10.Tm.{u_1}
    {A : Type u_1} [Ring A] [Algebra ℂ A] {n : ℕ}
    (E : Fin n → Fin n → A) (u : ℂ) (a b : Fin n) : A :=
  (if a = b then algebraMap ℂ A u else 0) + E a b

noncomputable def UpperTheory.Reformulated.B.Qf10.qminor.{u_1}
    {A : Type u_1} [Ring A] [Algebra ℂ A] {n t : ℕ}
    (E : Fin n → Fin n → A) (a b : Fin t → Fin n) (u : ℂ) : A :=
  ∑ σ : Equiv.Perm (Fin t),
    ((Equiv.Perm.sign σ : ℤ) : A) *
      (List.ofFn fun k : Fin t =>
        UpperTheory.Reformulated.B.Qf10.Tm E (u - (k.val : ℂ)) (a (σ k)) (b k)).prod

noncomputable def UpperTheory.Reformulated.B.Qf10.qdet.{u_1}
    {A : Type u_1} [Ring A] [Algebra ℂ A] {n : ℕ}
    (E : Fin n → Fin n → A) (u : ℂ) : A :=
  UpperTheory.Reformulated.B.Qf10.qminor E id id u

theorem UpperTheory.Reformulated.B.Qf10.casimir
    {V : Type} [AddCommGroup V] [_root_.Module ℂ V]
    (E : Fin 2 → Fin 2 → Module.End ℂ V)
    (hE : UpperTheory.Reformulated.B.Qf10.GlRel E)
    (k : ℂ) (φ : V)
    (h1 : E 0 0 φ + E 1 1 φ = 0)
    (h2 : E 0 1 φ - E 1 0 φ = (Complex.I * k) • φ)
    (h3 : E 0 0 φ - E 1 1 φ = Complex.I • (E 0 1 φ + E 1 0 φ))
    (u : ℂ) :
    UpperTheory.Reformulated.B.Qf10.qdet E (u + 1 / 2) φ =
      ((u + (k - 1) / 2) * (u - (k - 1) / 2)) • φ := by
  have rel : ∀ a b c d : Fin 2, E a b (E c d φ) - E c d (E a b φ) =
      (if b = c then E a d φ else 0) - (if d = a then E c b φ else 0) := by
    intro a b c d
    have h := congrArg (fun f : Module.End ℂ V => f φ) (hE a b c d)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    rw [h]
    split_ifs <;> simp
  have rab : E 0 0 (E 0 1 φ) - E 0 1 (E 0 0 φ) = E 0 1 φ := by simpa using rel 0 0 0 1
  have rac : E 0 0 (E 1 0 φ) - E 1 0 (E 0 0 φ) = -E 1 0 φ := by simpa using rel 0 0 1 0
  have rdb : E 1 1 (E 0 1 φ) - E 0 1 (E 1 1 φ) = -E 0 1 φ := by simpa using rel 1 1 0 1
  have rdc : E 1 1 (E 1 0 φ) - E 1 0 (E 1 1 φ) = E 1 0 φ := by simpa using rel 1 1 1 0
  have rbc : E 0 1 (E 1 0 φ) - E 1 0 (E 0 1 φ) = E 0 0 φ - E 1 1 φ := by simpa using rel 0 1 1 0
  have rad : E 0 0 (E 1 1 φ) - E 1 1 (E 0 0 φ) = 0 := by simpa using rel 0 0 1 1
  have t1 : ∀ X : Module.End ℂ V, X (E 0 0 φ) + X (E 1 1 φ) = 0 := fun X => by
    rw [← map_add (f := _), h1, map_zero]
  have t2 : ∀ X : Module.End ℂ V,
      X (E 0 1 φ) - X (E 1 0 φ) = (Complex.I * k) • X φ := fun X => by
    rw [← map_sub, h2, map_smul]
  have t3 : ∀ X : Module.End ℂ V, X (E 0 0 φ) - X (E 1 1 φ) =
      Complex.I • (X (E 0 1 φ) + X (E 1 0 φ)) := fun X => by
    rw [← map_sub, h3, map_smul, map_add (f := _)]
  have hc : (E 0 0 (E 0 0 φ) - E 0 0 (E 1 1 φ) - E 1 1 (E 0 0 φ) + E 1 1 (E 1 1 φ)) +
      (E 0 1 (E 0 1 φ) + E 0 1 (E 1 0 φ) + E 1 0 (E 0 1 φ) + E 1 0 (E 1 0 φ)) =
      (-2 * k) • φ := by
    linear_combination (norm := module)
      (t3 (E 0 0) - t3 (E 1 1) + Complex.I • t3 (E 0 1) + Complex.I • t3 (E 1 0)) +
        Complex.I • (rab + rac - rdb - rdc) + (2 * Complex.I) • h2 +
        Complex.I_sq • (E 0 1 (E 0 1 φ) + E 0 1 (E 1 0 φ) + E 1 0 (E 0 1 φ) + E 1 0 (E 1 0 φ) +
          (2 * k) • φ)
  have hw : E 0 1 (E 0 1 φ) - E 0 1 (E 1 0 φ) - E 1 0 (E 0 1 φ) + E 1 0 (E 1 0 φ) =
      (-k ^ 2) • φ := by
    linear_combination (norm := module)
      (t2 (E 0 1) - t2 (E 1 0)) + (Complex.I * k) • h2 + Complex.I_sq • (k ^ 2 • φ)
  have hu : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by decide
  have hne : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 := by decide
  have hq : ∀ v : ℂ, UpperTheory.Reformulated.B.Qf10.qdet E v φ =
      v • ((v - 1) • φ + E 1 1 φ) + ((v - 1) • E 0 0 φ + E 0 0 (E 1 1 φ)) - E 1 0 (E 0 1 φ) := by
    intro v
    unfold UpperTheory.Reformulated.B.Qf10.qdet UpperTheory.Reformulated.B.Qf10.qminor UpperTheory.Reformulated.B.Qf10.Tm
    rw [hu, Finset.sum_pair hne]
    simp [List.ofFn_succ, Module.algebraMap_end_apply]
    module
  rw [hq]
  linear_combination (norm := module)
    u • h1 + (1 / 4 : ℂ) • (t1 (E 0 0) + t1 (E 1 1)) + (1 / 2 : ℂ) • rad - (1 / 4 : ℂ) • hc +
      (1 / 4 : ℂ) • hw + (1 / 2 : ℂ) • rbc
