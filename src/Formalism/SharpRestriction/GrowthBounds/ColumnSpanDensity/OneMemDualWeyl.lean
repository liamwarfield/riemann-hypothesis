module

public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.ResidueClassCountOfTensorBasisInclusion

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.OneMemDualWeyl
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.LatticeSystems Formalism.GradedWeylDivisibility MvPolynomial

theorem dualWeyl_mul (R : Type*) [CommRing R] (r n : ℕ) (ν ν' : Fin n → ℕ) {F G : MvPolynomial (Fin r × Fin n) R}
    (hF : F ∈ dualWeyl R r n ν) (hG : G ∈ dualWeyl R r n ν') : F * G ∈ dualWeyl R r n (ν + ν') := by
  rw [dualWeyl, Submodule.mem_inf] at hF hG ⊢
  refine ⟨(mem_weightedHomogeneousSubmodule _ _ _ _).2
    (((mem_weightedHomogeneousSubmodule _ _ _ _).1 hF.1).mul
      ((mem_weightedHomogeneousSubmodule _ _ _ _).1 hG.1)), ?_⟩
  have hF2 := hF.2
  have hG2 := hG.2
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply,
    sub_eq_zero] at hF2 hG2 ⊢
  intro l j hlj
  rw [map_mul, map_mul, hF2 l j hlj, hG2 l j hlj]

theorem one_mem_dualWeyl (R : Type*) [CommRing R] (r n : ℕ) : (1 : MvPolynomial (Fin r × Fin n) R) ∈ dualWeyl R r n 0 := by
  rw [dualWeyl, Submodule.mem_inf]
  refine ⟨(mem_weightedHomogeneousSubmodule _ _ _ _).2 (isWeightedHomogeneous_one _ _), ?_⟩
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply,
    map_one, sub_self, implies_true]

section Ten

variable {R K : Type*} [CommRing R] [CommRing K] [Algebra R K] {S : Type*} [Fintype S] {k n : ℕ}

theorem tensorLat_mul (M N L : S → Submodule R (MvPolynomial (Fin k × Fin n) K))
    (h : ∀ s, ∀ F ∈ M s, ∀ G ∈ N s, F * G ∈ L s) :
    ∀ P ∈ tensorLat R K M, ∀ Q ∈ tensorLat R K N, P * Q ∈ tensorLat R K L := by
  intro P hP Q hQ
  have hmem : P * Q ∈ tensorLat R K M * tensorLat R K N := Submodule.mul_mem_mul hP hQ
  rw [tensorLat, tensorLat, Submodule.span_mul_span] at hmem
  refine (Submodule.span_le.2 ?_) hmem
  rintro x ⟨a, ⟨F, hF, rfl⟩, b, ⟨G, hG, rfl⟩, rfl⟩
  apply Submodule.subset_span
  refine ⟨fun s => F s * G s, fun s => h s _ (hF s) _ (hG s), ?_⟩
  simp [map_mul, Finset.prod_mul_distrib]

end Ten

theorem nuOf_zero (m : ℕ) : nuOf (0 : Fin (m + 1) → ℤ) = 0 := by
  funext t
  simp [nuOf]

theorem Vsp_eq (Kf : Type) [Field Kf] {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) (hdom : IsDominant lam0) :
    Vsp Kf lam0 = tensorLat Kf Kf (fun s => dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt lam0 s))) := by
  unfold Vsp
  congr 1
  funext s
  rw [if_pos (kp_lamAt_antitone lam0 hdom s)]

end Formalism.MainNotions.flipOneThree.Pf

end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.SingleWeightLatticeComparison
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility MvPolynomial

def wtPQ (m P Q : ℕ) : Fin (m + 1) → ℤ := fun i => if i = 0 then (P : ℤ) else if i = Fin.last m then -(Q : ℤ) else 0

def twoLat (O : Type) {Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] (m P Q : ℕ)
    (Λ : Submodule O (Fin (m + 1) → Kf)) : Submodule O (MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) Kf) :=
  tensorLat O Kf fun b : Bool => H0 O m (letterWt m (if b then P else Q) b) Λ

def twoSp (Kf : Type) [Field Kf] (m P Q : ℕ) : Submodule Kf (MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) Kf) :=
  tensorLat Kf Kf fun b : Bool => dualWeyl Kf (m + 1) (m + 1) (nuOf (letterWt m (if b then P else Q) b))

def SingleWeightLatticeComparison : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (m : ℕ), 2 ≤ m → ∀ (a P Q : ℕ), P + Q + 1 ≤ 8 * a →
    ∃ (i : ℕ → MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf →ₗ[R.Kf]
        MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) R.Kf)
      (pr : ℕ → MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) R.Kf →ₗ[R.Kf]
        MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf),
      (∀ x ∈ twoSp R.Kf m P Q, ∑ j ∈ Finset.range (min P Q + 1), i j (pr j x) = x) ∧
      (∀ j ≤ min P Q,
        (∀ x ∈ twoSp R.Kf m P Q, pr j x ∈ dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m (P - j) (Q - j)))) ∧
        (∀ y ∈ dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m (P - j) (Q - j))), i j y ∈ twoSp R.Kf m P Q)) ∧
      ∀ Λ : Submodule R.O (Fin (m + 1) → R.Kf), IsLattice R.O Λ → ∀ j ≤ min P Q,
        (∀ x ∈ twoLat R.O m P Q Λ,
          ((p : R.Kf) ^ ⌈((m : ℝ) + 2) * lgA p a m⌉₊) • pr j x ∈ H0 R.O m (wtPQ m (P - j) (Q - j)) Λ) ∧
        (∀ y ∈ H0 R.O m (wtPQ m (P - j) (Q - j)) Λ,
          ((p : R.Kf) ^ ⌈((m : ℝ) + 2) * lgA p a m⌉₊) • i j y ∈ twoLat R.O m P Q Λ)

end Formalism.MainNotions.flipOneThree.Pf

end
end
