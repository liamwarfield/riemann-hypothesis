module

public import Mathlib

@[expose] public section

/-!
# Transfer of Highest-Weight `K`-Types along `K`-Equivariant Maps on `L²(U(p, q))`

Sets up the indefinite unitary group `UJ ε ≤ GL_n(ℂ)` for a sign signature
`ε : Fin n → Bool`, its left Haar measure `muG ε`, its right-regular
representation `rreg ε` on `L2 ε = Lp ℂ 2 (muG ε)`, its maximal compact
subgroup `Kset ε` (the centralizer of `Jm ε` in `U(n)`), and the highest-weight
`K`-type predicate `IsKTypeOf` with compact-root dominance `CDom`.

The main theorem `hloweq_transfer` proves that any `ℂ`-linear endomorphism `A`
of `L2 ε` that intertwines the `K`-action and is injective on a `K`-type `S` of
highest weight `Λ` maps `S` onto another `K`-type `S.map A` of the same highest
weight `Λ`.
-/

namespace UpperTheory.Reformulated.B.Re3

noncomputable def Jm {n : ℕ} (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun a : Fin n => if ε a = true then 1 else -1

noncomputable def inUJ {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  g.conjTranspose * Jm ε * g = Jm ε

noncomputable def UJ {n : ℕ} (ε : Fin n → Bool) : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ where
  carrier := {g | inUJ ε g.val}
  one_mem' := by simp [inUJ]
  mul_mem' {g h} hg hh := by
    have hg' : g.val.conjTranspose * Jm ε * g.val = Jm ε := hg
    have hh' : h.val.conjTranspose * Jm ε * h.val = Jm ε := hh
    change (g.val * h.val).conjTranspose * Jm ε * (g.val * h.val) = Jm ε
    rw [Matrix.conjTranspose_mul]
    calc h.val.conjTranspose * g.val.conjTranspose * Jm ε * (g.val * h.val)
        = h.val.conjTranspose * (g.val.conjTranspose * Jm ε * g.val) * h.val := by
            simp only [Matrix.mul_assoc]
      _ = Jm ε := by rw [hg', hh']
  inv_mem' {g} hg := by
    have hg' : g.val.conjTranspose * Jm ε * g.val = Jm ε := hg
    change (g⁻¹).val.conjTranspose * Jm ε * (g⁻¹).val = Jm ε
    calc (g⁻¹).val.conjTranspose * Jm ε * (g⁻¹).val
        = (g⁻¹).val.conjTranspose * (g.val.conjTranspose * Jm ε * g.val) * (g⁻¹).val := by
            rw [hg']
      _ = (g.val * (g⁻¹).val).conjTranspose * Jm ε * (g.val * (g⁻¹).val) := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Jm ε := by rw [Units.mul_inv, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

@[reducible] noncomputable def instMeasurableSpaceUJ (n : ℕ) (ε : Fin n → Bool) :
    MeasurableSpace (UJ ε) :=
  borel (UJ ε)

attribute [local instance] instMeasurableSpaceUJ

theorem laurent_T_neg_one_mul_T_one (n : ℕ) (ε : Fin n → Bool) :
    LocallyCompactSpace (UJ ε) := by
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  have hc : IsClosed (UJ ε : Set (Matrix (Fin n) (Fin n) ℂ)ˣ) :=
    isClosed_eq
      ((Units.continuous_val.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
        Units.continuous_val)
      continuous_const
  exact hc.locallyCompactSpace

attribute [local instance] laurent_T_neg_one_mul_T_one

noncomputable def muG {n : ℕ} (ε : Fin n → Bool) : MeasureTheory.Measure (UJ ε) :=
  letI : BorelSpace (UJ ε) := ⟨rfl⟩
  MeasureTheory.Measure.haar

theorem algebra_smulCommClass_complex : (1 + 1 : ℕ).AtLeastTwo := ⟨le_refl 2⟩

@[reducible] noncomputable def L2 {n : ℕ} (ε : Fin n → Bool) : Type :=
  MeasureTheory.Lp ℂ 2 (muG ε)

noncomputable def d15 {n : ℕ} (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun a : Fin n => if ε a = true then 1 else -1

noncomputable def Kset {n : ℕ} (ε : Fin n → Bool) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {g | g ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ g * d15 ε = d15 ε * g}

theorem complex_normed_instance_compat : IsBoundedSMul ℂ ℂ := inferInstance

@[reducible] noncomputable def umat {n : ℕ} {ε : Fin n → Bool} (g : UJ ε) :
    Matrix (Fin n) (Fin n) ℂ :=
  g.val.val

open scoped Classical in
noncomputable def rregG {n : ℕ} (ε : Fin n → Bool) (y : UJ ε) : L2 ε →L[ℂ] L2 ε :=
  if hm : MeasureTheory.MeasurePreserving (fun x : UJ ε => x * y) (muG ε) (muG ε) then
    (MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ (fun x : UJ ε => x * y) hm).toContinuousLinearMap
  else 1

open scoped Classical in
noncomputable def rreg {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) :
    L2 ε →L[ℂ] L2 ε :=
  if h : ∃ y : UJ ε, umat y = g then rregG ε h.choose else 1

noncomputable def d21 {n : ℕ} (ε : Fin n → Bool) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {g | g ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ g * Jm ε = Jm ε * g}

noncomputable def IsKStableOn.{u_1} {n : ℕ} {H : Type u_1} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H)
    (S : Submodule ℂ H) : Prop :=
  ∀ g ∈ d21 ε, ∀ v ∈ S, σ g v ∈ S

noncomputable def IsWtOn.{u_1} {n : ℕ} {H : Type u_1} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (G : Set (Matrix (Fin n) (Fin n) ℂ))
    (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H) (μ : Fin n → ℝ) (v : H) : Prop :=
  ∀ θ : Fin n → ℝ,
    Matrix.diagonal (fun a : Fin n => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ G →
      σ (Matrix.diagonal fun a : Fin n => Complex.exp ((θ a : ℂ) * Complex.I)) v =
        Complex.exp ((∑ a : Fin n, μ a * θ a : ℝ) * Complex.I) • v

noncomputable def root {n : ℕ} (a b : Fin n) : Fin n → ℝ :=
  Pi.single a (1 : ℝ) - Pi.single b (1 : ℝ)

noncomputable def CDom {n : ℕ} (ε : Fin n → Bool) (μ Λ : Fin n → ℝ) : Prop :=
  ∃ c : Fin n → Fin n → ℕ,
    (∀ a b : Fin n, c a b ≠ 0 → a < b ∧ ε a = ε b) ∧
      Λ - μ = ∑ a : Fin n, ∑ b : Fin n, c a b • root a b

noncomputable def IsKTypeOf.{u_1} {n : ℕ} {H : Type u_1} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H)
    (Λ : Fin n → ℝ) (S : Submodule ℂ H) : Prop :=
  FiniteDimensional ℂ S ∧
    IsKStableOn ε σ S ∧
    (∀ S' ≤ S, IsKStableOn ε σ S' → S' = ⊥ ∨ S' = S) ∧
    (∃ v ∈ S, v ≠ 0 ∧ IsWtOn (d21 ε) σ Λ v) ∧
    (∀ μ v, v ∈ S → v ≠ 0 → IsWtOn (d21 ε) σ μ v → CDom ε μ Λ)

private theorem transfer_gen {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ε : Fin n → Bool} {Λ : Fin n → ℝ} (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H)
    (A : H →ₗ[ℂ] H) (hA : ∀ k ∈ d21 ε, ∀ x : H, A (σ k x) = σ k (A x))
    {S : Submodule ℂ H} (hinj : ∀ w ∈ S, A w = 0 → w = 0)
    (hS : IsKTypeOf ε σ Λ S) :
    IsKTypeOf ε σ Λ (Submodule.map A S) := by
  obtain ⟨hfd, hst, hirr, ⟨v, hvS, hv0, hvw⟩, hdom⟩ := hS
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
  · rintro g hg _ ⟨w, hw, rfl⟩
    exact ⟨σ g w, hst g hg w hw, hA g hg w⟩
  · intro S' hS' hst'
    have hT : IsKStableOn ε σ (S ⊓ Submodule.comap A S') := by
      intro g hg w hw
      refine ⟨hst g hg w hw.1, ?_⟩
      show A (σ g w) ∈ S'
      rw [hA g hg w]
      exact hst' g hg _ hw.2
    rcases hirr _ inf_le_left hT with h | h
    · left
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨w, hw, rfl⟩ := hS' hx
      have hw0 : w ∈ S ⊓ Submodule.comap A S' := ⟨hw, hx⟩
      rw [h, Submodule.mem_bot] at hw0
      simp [hw0]
    · right
      refine le_antisymm hS' ?_
      rintro _ ⟨w, hw, rfl⟩
      have hw1 : w ∈ S ⊓ Submodule.comap A S' := by rw [h]; exact hw
      exact hw1.2
  · refine ⟨A v, ⟨v, hvS, rfl⟩, fun h => hv0 (hinj v hvS h), ?_⟩
    intro θ hθ
    rw [← hA _ hθ, hvw θ hθ, map_smul]
  · rintro μ _ ⟨w, hw, rfl⟩ hw0 hwt
    refine hdom μ w hw (fun h => hw0 (by simp [h])) ?_
    intro θ hθ
    apply sub_eq_zero.mp
    apply hinj _ (S.sub_mem (hst _ hθ w hw) (S.smul_mem _ hw))
    rw [map_sub, map_smul, hA _ hθ, hwt θ hθ, sub_self]

theorem hloweq_transfer {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ}
    (A : L2 ε →ₗ[ℂ] L2 ε)
    (hA : ∀ k ∈ Kset ε, ∀ x : L2 ε, A (rreg ε k x) = rreg ε k (A x))
    {S : Submodule ℂ (L2 ε)} (hinj : ∀ w ∈ S, A w = 0 → w = 0)
    (hS : IsKTypeOf ε (rreg ε) Λ S) :
    IsKTypeOf ε (rreg ε) Λ (Submodule.map A S) :=
  transfer_gen (rreg ε) A hA hinj hS

end UpperTheory.Reformulated.B.Re3
