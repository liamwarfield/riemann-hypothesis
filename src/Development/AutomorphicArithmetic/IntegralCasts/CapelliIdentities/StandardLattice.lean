module

public import Mathlib

@[expose] public section

/-!
# Localization of `𝓞_K`-Lattices at a Rational Prime `l`

For a prime `l` and a number field `K`, constructs the localization `Rl l K = 𝓞_K ⊗_ℤ ℤ_{(l)}`
of the ring of integers at the multiplicative set `Ml l K` of rational integers not divisible
by `l`, defines the localized lattice `atL l K L = Rl · L ⊆ V`, and characterizes membership:
`x ∈ atL l K L ↔ ∃ s ∈ Ml l K, s • x ∈ L`.
-/

noncomputable def UpperTheory.Reformulated.B.StandardLattice.pZ (l : ℕ) : Ideal ℤ :=
  Ideal.span {(l : ℤ)}

theorem UpperTheory.Reformulated.B.StandardLattice.aux2
    (l : ℕ) [hl : Fact (Nat.Prime l)] :
    (UpperTheory.Reformulated.B.StandardLattice.pZ l).IsPrime := by
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl.out
  exact (Ideal.span_singleton_prime hp.ne_zero).mpr hp

attribute [local instance] UpperTheory.Reformulated.B.StandardLattice.aux2

@[reducible] noncomputable def UpperTheory.Reformulated.B.StandardLattice.Ml
    (l : ℕ) [Fact (Nat.Prime l)] (K : Type) [Field K] :
    Submonoid (NumberField.RingOfIntegers K) :=
  Algebra.algebraMapSubmonoid (NumberField.RingOfIntegers K)
    (UpperTheory.Reformulated.B.StandardLattice.pZ l).primeCompl

@[reducible] noncomputable def UpperTheory.Reformulated.B.StandardLattice.Rl
    (l : ℕ) [Fact (Nat.Prime l)] (K : Type) [Field K] : Type :=
  Localization (UpperTheory.Reformulated.B.StandardLattice.Ml l K)

theorem UpperTheory.Reformulated.B.StandardLattice.aux5
    (l : ℕ) [Fact (Nat.Prime l)] (K : Type) [Field K] :
    IsLocalization (UpperTheory.Reformulated.B.StandardLattice.Ml l K)
      (UpperTheory.Reformulated.B.StandardLattice.Rl l K) :=
  Localization.isLocalization

theorem UpperTheory.Reformulated.B.StandardLattice.aux6
    (l : ℕ) [Fact (Nat.Prime l)] (K : Type) [Field K] [NumberField K]
    (y : ↥(UpperTheory.Reformulated.B.StandardLattice.Ml l K)) :
    IsUnit (algebraMap (NumberField.RingOfIntegers K) K y) := by
  obtain ⟨y, n, hn, rfl⟩ := y
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn (Ideal.zero_mem _)
  refine isUnit_iff_ne_zero.mpr ?_
  simpa using hn0

noncomputable def UpperTheory.Reformulated.B.StandardLattice.rlToK
    (l : ℕ) [Fact (Nat.Prime l)] (K : Type) [Field K] [NumberField K] :
    UpperTheory.Reformulated.B.StandardLattice.Rl l K →+* K :=
  IsLocalization.lift (UpperTheory.Reformulated.B.StandardLattice.aux6 l K)

@[reducible] noncomputable def UpperTheory.Reformulated.B.StandardLattice.rlAlgebra
    (l : ℕ) [Fact (Nat.Prime l)] (K : Type) [Field K] [NumberField K] :
    Algebra (UpperTheory.Reformulated.B.StandardLattice.Rl l K) K :=
  (UpperTheory.Reformulated.B.StandardLattice.rlToK l K).toAlgebra

attribute [local instance] UpperTheory.Reformulated.B.StandardLattice.rlAlgebra

@[reducible] noncomputable def UpperTheory.Reformulated.B.StandardLattice.rlModule
    (l : ℕ) [Fact (Nat.Prime l)] (K : Type) [Field K] [NumberField K]
    (V : Type) [AddCommGroup V] [_root_.Module K V] :
    _root_.Module (UpperTheory.Reformulated.B.StandardLattice.Rl l K) V :=
  Module.compHom V (algebraMap (UpperTheory.Reformulated.B.StandardLattice.Rl l K) K)

attribute [local instance] UpperTheory.Reformulated.B.StandardLattice.rlModule

noncomputable def UpperTheory.Reformulated.B.StandardLattice.atL
    (l : ℕ) [Fact (Nat.Prime l)] (K : Type) [Field K] [NumberField K]
    {V : Type} [AddCommGroup V] [_root_.Module K V]
    [_root_.Module (NumberField.RingOfIntegers K) V]
    (L : Submodule (NumberField.RingOfIntegers K) V) :
    Submodule (UpperTheory.Reformulated.B.StandardLattice.Rl l K) V :=
  Submodule.span (UpperTheory.Reformulated.B.StandardLattice.Rl l K) (L : Set V)

theorem UpperTheory.Reformulated.B.StandardLattice.mem_atL_iff
    (l : ℕ) [Fact (Nat.Prime l)] (K : Type) [Field K] [NumberField K]
    {V : Type} [AddCommGroup V] [_root_.Module K V]
    [_root_.Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V]
    {L : Submodule (NumberField.RingOfIntegers K) V} {x : V} :
    x ∈ UpperTheory.Reformulated.B.StandardLattice.atL l K L ↔
      ∃ s ∈ UpperTheory.Reformulated.B.StandardLattice.Ml l K, s • x ∈ L := by
  have hact : ∀ (r : NumberField.RingOfIntegers K) (v : V),
      (algebraMap (NumberField.RingOfIntegers K)
        (UpperTheory.Reformulated.B.StandardLattice.Rl l K) r) • v = r • v := by
    intro r v
    change UpperTheory.Reformulated.B.StandardLattice.rlToK l K (algebraMap _ _ r) • v = r • v
    unfold UpperTheory.Reformulated.B.StandardLattice.rlToK
    rw [IsLocalization.lift_eq, algebraMap_smul]
  haveI : IsScalarTower (NumberField.RingOfIntegers K)
      (UpperTheory.Reformulated.B.StandardLattice.Rl l K) V :=
    IsScalarTower.of_algebraMap_smul hact
  unfold UpperTheory.Reformulated.B.StandardLattice.atL
  rw [IsLocalization.mem_span_iff (UpperTheory.Reformulated.B.StandardLattice.Ml l K), Submodule.span_eq]
  constructor
  · rintro ⟨y, hy, z, rfl⟩
    refine ⟨z, z.2, ?_⟩
    rw [← hact, smul_smul, IsLocalization.mk'_spec', map_one, one_smul]
    exact hy
  · rintro ⟨s, hs, hx⟩
    refine ⟨s • x, hx, ⟨s, hs⟩, ?_⟩
    rw [← hact, smul_smul]
    have := IsLocalization.mk'_spec (UpperTheory.Reformulated.B.StandardLattice.Rl l K)
      (1 : NumberField.RingOfIntegers K)
      (⟨s, hs⟩ : UpperTheory.Reformulated.B.StandardLattice.Ml l K)
    rw [this, map_one, one_smul]
