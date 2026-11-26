module

public import Mathlib

@[expose] public section

/-!
# Inversion Invariance of Unimodular Haar Measure on `U(p, q)`

For any sign signature `ε : Fin n → Bool`, let `Jm ε = diag(±1)` and let
`UJ ε ≤ GL_n(ℂ)` be the indefinite unitary group `{g | gᴴ * Jm ε * g = Jm ε}`,
equipped with its Borel measurable space and left Haar measure `muG ε`.

The main theorem `invInvariant_of` proves that if `muG ε` is unimodular (i.e.,
also right-translation invariant), then it is invariant under inversion
`x ↦ x⁻¹`. On any locally compact topological group, the pushforward of a
unimodular left Haar measure under inversion is a positive scalar multiple
`c • μ`, and applying the involution twice yields `c² = 1`, hence `c = 1`.
-/

namespace UpperTheory.Reformulated.B.InvolutionInvariants

noncomputable def Jm {n : ℕ} (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun a : Fin n => if ε a = true then 1 else -1

noncomputable def inUJ {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  g.conjTranspose * Jm ε * g = Jm ε

noncomputable def UJ {n : ℕ} (ε : Fin n → Bool) : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ where
  carrier := {g | inUJ ε g.val}
  one_mem' := by simp [inUJ]
  mul_mem' {g h} hg hh := by
    change inUJ ε _ at hg hh ⊢
    unfold inUJ at hg hh ⊢
    rw [Units.val_mul, Matrix.conjTranspose_mul]
    calc (h.val).conjTranspose * (g.val).conjTranspose * Jm ε * (g.val * h.val)
        = (h.val).conjTranspose * ((g.val).conjTranspose * Jm ε * g.val) * h.val := by
            simp only [Matrix.mul_assoc]
      _ = Jm ε := by rw [hg, hh]
  inv_mem' {g} hg := by
    change inUJ ε _ at hg ⊢
    unfold inUJ at hg ⊢
    have h1 : g.val * (g⁻¹).val = 1 := Units.mul_inv g
    calc ((g⁻¹).val).conjTranspose * Jm ε * (g⁻¹).val
        = ((g⁻¹).val).conjTranspose * ((g.val).conjTranspose * Jm ε * g.val) * (g⁻¹).val := by
            rw [hg]
      _ = (g.val * (g⁻¹).val).conjTranspose * Jm ε * (g.val * (g⁻¹).val) := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Jm ε := by rw [h1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

@[reducible] noncomputable def instMeasurableSpaceUJ (n : ℕ) (ε : Fin n → Bool) :
    MeasurableSpace (UJ ε) :=
  borel (UJ ε)

attribute [local instance] instMeasurableSpaceUJ

theorem laurent_T_neg_one_mul_T_one (n : ℕ) (ε : Fin n → Bool) :
    LocallyCompactSpace (UJ ε) := by
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  have hc : IsClosed {g : (Matrix (Fin n) (Fin n) ℂ)ˣ |
      g.val.conjTranspose * Jm ε * g.val = Jm ε} :=
    isClosed_eq
      ((Units.continuous_val.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
        Units.continuous_val)
      continuous_const
  exact hc.locallyCompactSpace

attribute [local instance] laurent_T_neg_one_mul_T_one

noncomputable def muG {n : ℕ} (ε : Fin n → Bool) : MeasureTheory.Measure (UJ ε) :=
  letI : BorelSpace (UJ ε) := ⟨rfl⟩
  MeasureTheory.Measure.haar

noncomputable def Unimodular : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (g : UJ ε),
    MeasureTheory.Measure.map (fun x : UJ ε => x * g) (muG ε) = muG ε

noncomputable def InvInvariant : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool),
    MeasureTheory.Measure.map (fun x : UJ ε => x⁻¹) (muG ε) = muG ε

open scoped Pointwise in
open MeasureTheory MeasureTheory.Measure in
private theorem haar_map_inv {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G]
    (h : ∀ g : G, Measure.map (fun x => x * g) (haar : Measure G) = haar) :
    Measure.map (fun x => x⁻¹) (haar : Measure G) = haar := by
  have : (haar : Measure G).IsMulRightInvariant := ⟨h⟩
  have : (haar : Measure G).Regular := regular_haarMeasure
  obtain ⟨c, hc⟩ : ∃ c : ENNReal, (haar : Measure G).inv = c • haar :=
    ⟨haarScalarFactor (haar : Measure G).inv haar,
      isMulLeftInvariant_eq_smul_of_regular (haar : Measure G).inv haar⟩
  have K : TopologicalSpace.PositiveCompacts G := Classical.arbitrary _
  have h0 : (haar : Measure G) K ≠ 0 := (measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
  have ht : (haar : Measure G) K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have h1 : ∀ s : Set G, (haar : Measure G) s⁻¹ = c * haar s := fun s => by
    rw [← MeasureTheory.Measure.inv_apply, hc, smul_apply, smul_eq_mul]
  have h2 : c ^ 2 * (haar : Measure G) K = 1 ^ 2 * (haar : Measure G) K := by
    rw [pow_two, mul_assoc, ← h1, ← h1, inv_inv, one_pow, one_mul]
  have h3 : c = 1 :=
    (ENNReal.pow_right_strictMono two_ne_zero).injective ((ENNReal.mul_left_inj h0 ht).1 h2)
  rw [h3, one_smul] at hc
  exact hc

theorem invInvariant_of : Unimodular → InvInvariant := fun h n ε =>
  letI : BorelSpace (UJ ε) := ⟨rfl⟩
  haar_map_inv (G := UJ ε) (h n ε)

end UpperTheory.Reformulated.B.InvolutionInvariants
