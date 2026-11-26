module

public import Mathlib

@[expose] public section

/-!
# Block-Diagonal `GL` Embeddings and Open Fixer Subgroups

Defines the upper-left block embedding `blkAt : GL_n(k) →* GL_N(k)` (for `n ≤ N`)
via `A ↦ diag(A, I_{N-n})`, smoothness of a topological group representation
(`IsSmooth`), and the predicate `FixK` asserting that a vector is fixed by an
embedded subgroup `K ≤ GL_{m+1}(k)`.

The main theorem `exists_fixK` proves that for any smooth complex representation
`π` of `GL_N(k)` over a nonarchimedean local field `k` and any two vectors
`v, w : V`, there exists an open subgroup `K ≤ GL_{m+1}(k)` fixing both `v` and
`w` (constructed as the preimage of the intersection of their stabilizers under
the continuous homomorphism `blkAt`).
-/

namespace UpperTheory.Reformulated.B.BlockHomomorphism

noncomputable def IsSmooth {k G V : Type} [Field k] [Group G] [AddCommGroup V]
    [_root_.Module k V] [TopologicalSpace G] (ρ : Representation k G V) : Prop :=
  ∀ v : V, IsOpen {g : G | ρ g v = v}

noncomputable def glCongr (k : Type) [Field k] {a b : ℕ} (h : a = b) :
    GL (Fin a) k →* GL (Fin b) k :=
  Units.map (Matrix.reindexAlgEquiv k k (finCongr h)).toMulEquiv.toMonoidHom

noncomputable def blkHom (k : Type) [Field k] (n r : ℕ) :
    Matrix (Fin n) (Fin n) k →* Matrix (Fin n ⊕ Fin r) (Fin n ⊕ Fin r) k where
  toFun A := Matrix.fromBlocks A 0 0 1
  map_one' := Matrix.fromBlocks_one
  map_mul' A B := by simp [Matrix.fromBlocks_multiply]

noncomputable def blkGL (k : Type) [Field k] (n r : ℕ) :
    GL (Fin n) k →* GL (Fin (n + r)) k :=
  Units.map
    ((Matrix.reindexAlgEquiv k k finSumFinEquiv).toMulEquiv.toMonoidHom.comp (blkHom k n r))

noncomputable def blkAt (k : Type) [Field k] (n N : ℕ) (h : n ≤ N) :
    GL (Fin n) k →* GL (Fin N) k :=
  (glCongr k (Nat.add_sub_cancel' h)).comp (blkGL k n (N - n))

noncomputable def FixK {k : Type} [Field k] {m N : ℕ} (h : m + 1 ≤ N)
    {V : Type} [AddCommGroup V] [_root_.Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (K : Subgroup (GL (Fin (m + 1)) k)) (v : V) : Prop :=
  ∀ g ∈ K, π (blkAt k (m + 1) N h g) v = v

private theorem continuous_blkAt {k : Type} [Field k] [TopologicalSpace k]
    (n N : ℕ) (h : n ≤ N) : Continuous (blkAt k n N h) := by
  have h1 : Continuous (blkGL k n (N - n)) := by
    unfold blkGL
    apply Continuous.units_map
    change Continuous fun A : Matrix (Fin n) (Fin n) k =>
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks A 0 0 (1 : Matrix (Fin (N - n)) (Fin (N - n)) k))
    exact (Continuous.matrix_fromBlocks continuous_id continuous_const continuous_const
      continuous_const).matrix_reindex _ _
  have h2 : ∀ {a b : ℕ} (e : a = b), Continuous (glCongr k e) := by
    intro a b e
    unfold glCongr
    apply Continuous.units_map
    change Continuous fun A : Matrix (Fin a) (Fin a) k =>
      Matrix.reindex (finCongr e) (finCongr e) A
    exact continuous_id.matrix_reindex _ _
  exact (h2 _).comp h1

private def fixer {G V : Type} [Group G] [AddCommGroup V] [_root_.Module ℂ V]
    (π : Representation ℂ G V) (v : V) : Subgroup G where
  carrier := {g | π g v = v}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [map_mul, mul_apply_eq_comp, hb, ha]
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    calc π a⁻¹ v = π a⁻¹ (π a v) := by rw [ha]
      _ = v := by
          rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one, one_apply_eq_self]

theorem exists_fixK {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {m N : ℕ} {h : m + 2 ≤ N} {V : Type}
    [AddCommGroup V] [_root_.Module ℂ V] {π : Representation ℂ (GL (Fin N) k) V}
    (hπ : IsSmooth π) (v w : V) :
    ∃ K : Subgroup (GL (Fin (m + 1)) k),
      IsOpen (K : Set (GL (Fin (m + 1)) k)) ∧
        FixK (by omega) π K v ∧ FixK (by omega) π K w := by
  have hle : m + 1 ≤ N := by omega
  refine ⟨(fixer π v ⊓ fixer π w).comap (blkAt k (m + 1) N hle), ?_,
    fun _ hg => hg.1, fun _ hg => hg.2⟩
  exact ((hπ v).inter (hπ w)).preimage (continuous_blkAt (m + 1) N hle)

end UpperTheory.Reformulated.B.BlockHomomorphism
