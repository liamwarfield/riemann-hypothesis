module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.XdualExt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.CardUnion
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.cardUnion :
    ∀ (P : Type) (S : ℕ → Set P) (b : ℕ), Monotone S → (∀ x, ∃ n, x ∈ S n) → (∀ n, CardLe (S n) b) → CardLe P b := by
  intro P S b hmono hcov hcard
  choose m hm using hcov
  have key : ∀ T : Finset P, T.card ≤ b := by
    intro T
    classical
    obtain ⟨hfN, hbN⟩ := hcard (T.sup m)
    have hsub : (↑T : Set P) ⊆ S (T.sup m) := by
      intro x hx
      exact hmono (Finset.le_sup (f := m) hx) (hm x)
    have hfin : (S (T.sup m)).Finite := Set.toFinite _
    have h1 := Nat.card_mono hfin hsub
    have h2 : Nat.card (↑T : Set P) = T.card := by simp
    omega
  have hfin : Finite P := by
    by_contra hnot
    rw [not_finite_iff_infinite] at hnot
    obtain ⟨T, hT⟩ := Infinite.exists_subset_card_eq P (b + 1)
    have := key T
    omega
  refine ⟨hfin, ?_⟩
  have := Fintype.ofFinite P
  classical
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
  exact key _
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.infRk :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (N r : ℕ) (U : Subgroup (G F Ω)), N ≠ 0 → IsClosed (U : Set (G F Ω)) → (∀ n, 2 ≤ n → XRk l N (levU l U n) r) → XRk l N (cycU l U) r := by
  intro F Ω _ _ _ _ _ l _ N r U hN hU h
  have anti : ∀ {m n : ℕ}, m ≤ n → levU l U n ≤ levU l U m := fun hmn =>
    inf_le_inf_left _ (Subgroup.comap_mono (KStar.TotallyRealRoots.princ_anti hmn))
  have down : ∀ {m n : ℕ} (hmn : m ≤ n) (ψ : ↥(levU l U m) → ZMod l),
      ψ ∈ XDual N (levU l U m) (ZMod l) (ZMod l) →
      restr (ZMod l) (ZMod l) (anti hmn) ψ ∈ XDual N (levU l U n) (ZMod l) (ZMod l) := by
    intro m n hmn ψ hψ
    exact (restrMem F Ω N _ _ (anti hmn) (ZMod l) (ZMod l) 1).1 (Submodule.mem_map_of_mem hψ)
  have comp : ∀ {m n : ℕ} (hmn : m ≤ n) (ψ : ↥(levU l U m) → ZMod l),
      restr (ZMod l) (ZMod l) (cycU_le_levU l U n) (restr (ZMod l) (ZMod l) (anti hmn) ψ)
        = restr (ZMod l) (ZMod l) (cycU_le_levU l U m) ψ := fun _ _ => rfl
  unfold XRk
  let X := XDual N (cycU l U) (ZMod l) (ZMod l)
  let S : ℕ → Set X := fun n => {φ | ∃ ψ ∈ XDual N (levU l U (n + 2)) (ZMod l) (ZMod l),
    restr (ZMod l) (ZMod l) (cycU_le_levU l U (n + 2)) ψ = (φ : ↥(cycU l U) → ZMod l)}
  apply cardUnion X S
  · intro m n hmn φ hφ
    obtain ⟨ψ, hψ, e⟩ := hφ
    have hmn' : m + 2 ≤ n + 2 := by omega
    exact ⟨_, down hmn' ψ hψ, (comp hmn' ψ).trans e⟩
  · intro φ
    obtain ⟨n, ψ, hψ, e⟩ := xdualExt F Ω l N U (ZMod l) (ZMod l) hN hU φ.1 φ.2
    have hn : n ≤ n + 2 := by omega
    exact ⟨n, _, down hn ψ hψ, (comp hn ψ).trans e⟩
  · intro n
    obtain ⟨hfin, hcard⟩ := h (n + 2) (by omega)
    let f : ↥(XDual N (levU l U (n + 2)) (ZMod l) (ZMod l)) → X := fun ψ =>
      ⟨restr (ZMod l) (ZMod l) (cycU_le_levU l U (n + 2)) ψ.1,
        (restrMem F Ω N _ _ (cycU_le_levU l U (n + 2)) (ZMod l) (ZMod l) 1).1
          (Submodule.mem_map_of_mem ψ.2)⟩
    have hsub : S n ⊆ Set.range f := by
      rintro φ ⟨ψ, hψ, e⟩
      exact ⟨⟨ψ, hψ⟩, Subtype.ext e⟩
    refine ⟨((Set.finite_range f).subset hsub).to_subtype, ?_⟩
    calc Nat.card (S n) ≤ Nat.card (Set.range f) := Nat.card_mono (Set.finite_range f) hsub
      _ ≤ Nat.card ↥(XDual N (levU l U (n + 2)) (ZMod l) (ZMod l)) := Finite.card_range_le f
      _ ≤ l ^ r := hcard
