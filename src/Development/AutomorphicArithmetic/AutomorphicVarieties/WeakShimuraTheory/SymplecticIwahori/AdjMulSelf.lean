module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SgnMulSelf

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.OfMap
noncomputable section

open IsLocalRing Polynomial UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.Ws.Pp

def SpTri {ι A C : Type} [CommRing A] [CommRing C] (M : ι → M4 A) (P : ι → Fin 4 → A[X]) (φ : A →+* C) (u : M4 C) : Prop :=
  IsGSp 1 u ∧ ∀ g, IsUp (adj u * (M g).map φ * u) ∧ ∀ i, (P g i).eval₂ φ ((adj u * (M g).map φ * u) i i) = 0

def Dist {A : Type} [CommRing A] (I : Ideal A) (p : A[X]) : Prop := p.Monic ∧ ∀ n < p.natDegree, p.coeff n ∈ I

theorem SpTri.map {ι A C C' : Type} [CommRing A] [CommRing C] [CommRing C'] {M : ι → M4 A} {P : ι → Fin 4 → A[X]}
    {φ : A →+* C} {u : M4 C} (h : SpTri M P φ u) (ψ : C →+* C') : SpTri M P (ψ.comp φ) (u.map ψ) := by
  have a : ∀ Y : M4 C, adj (Y.map ψ) = (adj Y).map ψ := fun Y => by
    ext i j
    simp only [adj_apply, Matrix.map_apply, map_zsmul]
  have e : ∀ g, adj (u.map ψ) * (M g).map (ψ.comp φ) * u.map ψ = (adj u * (M g).map φ * u).map ψ := fun g => by
    rw [a, Matrix.map_mul, Matrix.map_mul]
    rfl
  refine ⟨?_, fun g => ⟨fun i j hij => ?_, fun i => ?_⟩⟩
  · have := h.1
    unfold IsGSp at this ⊢
    rw [a, ← Matrix.map_mul, this, one_smul, one_smul, Matrix.map_one _ (map_zero ψ) (map_one ψ)]
  · rw [e, Matrix.map_apply, (h.2 g).1 i j hij, map_zero]
  · rw [e, Matrix.map_apply, ← hom_eval₂, (h.2 g).2 i, map_zero]

theorem SpTri.of_map {ι A C C' : Type} [CommRing A] [CommRing C] [CommRing C'] {M : ι → M4 A} {P : ι → Fin 4 → A[X]}
    {φ : A →+* C} {u : M4 C} (ψ : C →+* C') (hψ : Function.Injective ψ) (h : SpTri M P (ψ.comp φ) (u.map ψ)) :
    SpTri M P φ u := by
  have a : ∀ Y : M4 C, adj (Y.map ψ) = (adj Y).map ψ := fun Y => by
    ext i j
    simp only [adj_apply, Matrix.map_apply, map_zsmul]
  have e : ∀ g, adj (u.map ψ) * (M g).map (ψ.comp φ) * u.map ψ = (adj u * (M g).map φ * u).map ψ := fun g => by
    rw [a, Matrix.map_mul, Matrix.map_mul]
    rfl
  refine ⟨?_, fun g => ⟨fun i j hij => hψ ?_, fun i => hψ ?_⟩⟩
  · have := h.1
    unfold IsGSp at this ⊢
    rw [a, ← Matrix.map_mul, one_smul, ← Matrix.map_one ψ (map_zero ψ) (map_one ψ)] at this
    rw [one_smul]
    exact Matrix.map_injective hψ this
  · have := (h.2 g).1 i j hij
    rwa [e, Matrix.map_apply, ← map_zero ψ] at this
  · have := (h.2 g).2 i
    rwa [e, Matrix.map_apply, ← hom_eval₂, ← map_zero ψ] at this

end UpperTheory.V.Ws.Pp

end
end

open UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.Ws.Pp

variable {R : Type} [CommRing R]

theorem isUp_iff (X : M4 R) : IsUp X ↔ X.BlockTriangular id := by
  unfold IsUp
  exact ⟨fun h i j hij => h i j hij, fun h i j hij => h hij⟩

theorem IsUp_mul {X Y : M4 R} (hX : IsUp X) (hY : IsUp Y) : IsUp (X * Y) := by
  rw [isUp_iff] at hX hY ⊢
  exact hX.mul hY

theorem IsUp_adj {X : M4 R} (hX : IsUp X) : IsUp (adj X) := fun i j h => by
  rw [adj_apply, hX j.rev i.rev (Fin.rev_lt_rev.2 h), smul_zero]

theorem IsUp_inv {b : (M4 R)ˣ} (hb : IsUp (b : M4 R)) : IsUp ((b⁻¹ : (M4 R)ˣ) : M4 R) := by
  rw [isUp_iff] at hb ⊢
  haveI := b.invertible
  rw [Matrix.coe_units_inv]
  exact Matrix.blockTriangular_inv_of_blockTriangular hb

theorem IsUp_diag {X Y : M4 R} (hX : IsUp X) (hY : IsUp Y) (i : Fin 4) : (X * Y) i i = X i i * Y i i := by
  rw [isUp_iff] at hX hY
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hX h, zero_mul]
    · rw [hY h, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem upConj {a b X : M4 R} (hab : a * b = 1) (ha : IsUp a) (hb : IsUp b) (hX : IsUp X) :
    IsUp (a * X * b) ∧ ∀ i, (a * X * b) i i = X i i := by
  have hax : IsUp (a * X) := IsUp_mul ha hX
  refine ⟨IsUp_mul hax hb, fun i => ?_⟩
  rw [IsUp_diag hax hb, IsUp_diag ha hX]
  have h1 : a i i * b i i = 1 := by
    rw [← IsUp_diag ha hb, hab]
    simp
  calc a i i * X i i * b i i = X i i * (a i i * b i i) := by ring
    _ = X i i := by rw [h1, mul_one]

theorem adj_mul_self {u : M4 R} (h : IsGSp 1 u) : adj u * u = 1 := h.trans (one_smul _ _)

theorem mul_adj_self {u : M4 R} (h : IsGSp 1 u) : u * adj u = 1 := mul_eq_one_comm.1 (adj_mul_self h)

end UpperTheory.V.Ws.Pp
